from __future__ import annotations

import pytest

from src.integration.autotrader_signal_registry import (
    ExternalSignalSourceRegistry,
    ExternalSignalSourceRegistryEntry,
)
from src.integration.autotrader_signals import (
    AutoTraderObservationPacket,
    ExternalSignalObservation,
    QuoteReceiptSignalPacket,
    SignalSourceKind,
    SignalTrustTier,
)
from src.kernels.python.strategy_observation_packet_contract_v1_adapter import (
    check_strategy_observation_packet_contract,
)


def _primary(**overrides: object) -> QuoteReceiptSignalPacket:
    kwargs: dict[str, object] = {
        "current_epoch": 5,
        "quote_epoch": 5,
        "asset_in": "A",
        "asset_out": "B",
        "amount_in": 100,
        "amount_out": 150,
        "receipt_hash": "receipt.hash.1",
        "source_kind": SignalSourceKind.ROUTE_QUOTE_RECEIPT,
        "trust_tier": SignalTrustTier.VERIFIED,
        "quote_receipt_present": True,
        "quote_receipt_verified": True,
        "quote_epoch_present": True,
        "source_available": True,
        "auth_ok": True,
        "binding_ok": True,
    }
    kwargs.update(overrides)
    return QuoteReceiptSignalPacket(**kwargs)


def _advisory_external(**overrides: object) -> ExternalSignalObservation:
    kwargs: dict[str, object] = {
        "signal_id": "sig.news.1",
        "source_id": "feed.news.alpha",
        "source_kind": SignalSourceKind.ADVISORY_EXTERNAL,
        "trust_tier": SignalTrustTier.ADVISORY,
        "freshness_ok": True,
        "auth_ok": False,
        "advisory_only": True,
    }
    kwargs.update(overrides)
    return ExternalSignalObservation(**kwargs)


def _trusted_external(**overrides: object) -> ExternalSignalObservation:
    kwargs: dict[str, object] = {
        "signal_id": "sig.oracle.1",
        "source_id": "oracle.alpha",
        "source_kind": SignalSourceKind.ATTESTED_EXTERNAL,
        "trust_tier": SignalTrustTier.VERIFIED,
        "freshness_ok": True,
        "auth_ok": True,
        "advisory_only": False,
    }
    kwargs.update(overrides)
    return ExternalSignalObservation(**kwargs)


def _signal_source_registry() -> ExternalSignalSourceRegistry:
    return ExternalSignalSourceRegistry(
        entries=(
            ExternalSignalSourceRegistryEntry(
                source_id="feed.news.alpha",
                source_kind=SignalSourceKind.ADVISORY_EXTERNAL,
                allowed_trust_tiers=(SignalTrustTier.ADVISORY,),
                require_advisory_only=True,
                require_auth=False,
                require_freshness=True,
            ),
            ExternalSignalSourceRegistryEntry(
                source_id="oracle.alpha",
                source_kind=SignalSourceKind.ATTESTED_EXTERNAL,
                allowed_trust_tiers=(SignalTrustTier.ATTESTED, SignalTrustTier.VERIFIED),
                require_advisory_only=False,
                require_auth=True,
                require_freshness=True,
            ),
        )
    )


def test_observation_packet_contract_accepts_trusted_and_advisory_modes() -> None:
    trusted_packet = AutoTraderObservationPacket(
        current_epoch=5,
        primary_signal=_primary(),
        external_signals=(_advisory_external(), _trusted_external()),
        signal_source_registry=_signal_source_registry(),
    )
    trusted_result = check_strategy_observation_packet_contract(packet=trusted_packet)
    assert trusted_result.ok is True
    assert trusted_result.trusted_primary_ok is True
    assert trusted_result.external_signal_count == 2
    assert trusted_result.advisory_external_count == 1
    assert trusted_result.trusted_external_count == 1
    assert trusted_result.error is None

    advisory_packet = AutoTraderObservationPacket(
        current_epoch=5,
        primary_signal=_primary(
            source_kind=SignalSourceKind.ADVISORY_EXTERNAL,
            trust_tier=SignalTrustTier.ADVISORY,
        ),
        external_signals=(_advisory_external(signal_id="sig.news.2"),),
    )
    advisory_result = check_strategy_observation_packet_contract(packet=advisory_packet)
    assert advisory_result.ok is True
    assert advisory_result.primary_mode_ok is True
    assert advisory_result.trusted_primary_ok is False

    local_packet = AutoTraderObservationPacket(
        current_epoch=5,
        primary_signal=_primary(
            source_kind=SignalSourceKind.LOCAL_PROTOCOL_STATE,
            trust_tier=SignalTrustTier.PROTOCOL,
        ),
    )
    local_result = check_strategy_observation_packet_contract(packet=local_packet)
    assert local_result.ok is True
    assert local_result.trusted_primary_ok is True
    assert local_packet.trusted_primary() is True

    attested_packet = AutoTraderObservationPacket(
        current_epoch=5,
        primary_signal=_primary(
            source_kind=SignalSourceKind.ATTESTED_EXTERNAL,
            trust_tier=SignalTrustTier.ATTESTED,
        ),
    )
    attested_result = check_strategy_observation_packet_contract(packet=attested_packet)
    assert attested_result.ok is True
    assert attested_result.trusted_primary_ok is True
    assert attested_packet.trusted_primary() is True


def test_observation_packet_contract_rejects_bad_primary_mode_and_packet() -> None:
    with pytest.raises(
        ValueError,
        match="observation packet contract rejected: primary_signal_mode_invalid",
    ):
        AutoTraderObservationPacket(
            current_epoch=5,
            primary_signal=_primary(
                source_kind=SignalSourceKind.ROUTE_QUOTE_RECEIPT,
                trust_tier=SignalTrustTier.ADVISORY,
            ),
        )

    with pytest.raises(
        ValueError,
        match="observation packet contract rejected: primary_signal_invalid",
    ):
        AutoTraderObservationPacket(
            current_epoch=5,
            primary_signal=_primary(quote_receipt_verified=False),
        )


def test_observation_packet_contract_rejects_ambiguous_external_partition() -> None:
    ambiguous = _trusted_external(signal_id="sig.oracle.2", advisory_only=True)

    with pytest.raises(
        ValueError,
        match="observation packet contract rejected: external_signal_partition_invalid",
    ):
        AutoTraderObservationPacket(
            current_epoch=5,
            primary_signal=_primary(),
            external_signals=(ambiguous,),
        )


def test_observation_packet_contract_rejects_bad_types() -> None:
    with pytest.raises(TypeError, match="packet must be an AutoTraderObservationPacket"):
        check_strategy_observation_packet_contract(packet="bad")  # type: ignore[arg-type]
