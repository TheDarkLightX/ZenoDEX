from __future__ import annotations

import pytest

import src.integration.autotrader_signal_registry as signal_registry
from src.core.quote_receipts import make_route_quote_receipt
from src.core.routing import best_route_exact_in_2hop
from src.integration.autotrader_signal_registry import (
    ExternalSignalSourceRegistry,
    ExternalSignalSourceRegistryEntry,
    external_signal_source_registry_entry_from_dict,
    external_signal_source_registry_from_object,
)
from src.integration.autotrader_signals import (
    ExternalSignalObservation,
    SignalSourceKind,
    SignalTrustTier,
    build_autotrader_observation_packet,
    build_quote_receipt_signal_packet,
)
from src.state.pools import PoolState, PoolStatus


def _pool(pid: str, a0: str, a1: str, r0: int, r1: int) -> PoolState:
    return PoolState(
        pool_id=pid,
        asset0=min(a0, a1),
        asset1=max(a0, a1),
        reserve0=r0 if a0 < a1 else r1,
        reserve1=r1 if a0 < a1 else r0,
        fee_bps=0,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _market() -> tuple[dict[str, PoolState], dict[str, object]]:
    pools = {"p_ab": _pool("p_ab", "A", "B", 1_000, 2_000)}
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=100)
    assert quote is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools, quote_epoch=5)
    return pools, receipt


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


def _advisory_external(**overrides: object) -> ExternalSignalObservation:
    kwargs: dict[str, object] = {
        "signal_id": "sig.news.1",
        "source_id": "news.alpha",
        "source_kind": SignalSourceKind.ADVISORY_EXTERNAL,
        "trust_tier": SignalTrustTier.ADVISORY,
        "freshness_ok": True,
        "auth_ok": True,
        "advisory_only": True,
    }
    kwargs.update(overrides)
    return ExternalSignalObservation(**kwargs)


def _registry(**overrides: object) -> ExternalSignalSourceRegistry:
    entry_kwargs: dict[str, object] = {
        "source_id": "oracle.alpha",
        "source_kind": SignalSourceKind.ATTESTED_EXTERNAL,
        "allowed_trust_tiers": (SignalTrustTier.ATTESTED, SignalTrustTier.VERIFIED),
        "require_auth": True,
        "require_freshness": True,
    }
    entry_kwargs.update(overrides)
    return ExternalSignalSourceRegistry(entries=(ExternalSignalSourceRegistryEntry(**entry_kwargs),))


def _advisory_registry(**overrides: object) -> ExternalSignalSourceRegistry:
    entry_kwargs: dict[str, object] = {
        "source_id": "news.alpha",
        "source_kind": SignalSourceKind.ADVISORY_EXTERNAL,
        "allowed_trust_tiers": (SignalTrustTier.ADVISORY,),
        "require_auth": True,
        "require_freshness": True,
        "require_advisory_only": True,
    }
    entry_kwargs.update(overrides)
    return ExternalSignalSourceRegistry(entries=(ExternalSignalSourceRegistryEntry(**entry_kwargs),))


def test_signal_source_registry_entry_and_loader_roundtrip() -> None:
    entry = external_signal_source_registry_entry_from_dict(
        {
            "source_id": "oracle.alpha",
            "source_kind": "attested_external",
            "allowed_trust_tiers": ["verified", "verified", "attested"],
            "require_auth": True,
            "require_freshness": True,
            "tags": ["oracle", "oracle"],
        }
    )
    assert entry.allowed_trust_tiers == (SignalTrustTier.VERIFIED, SignalTrustTier.ATTESTED)
    assert entry.tags == ("oracle",)

    registry = external_signal_source_registry_from_object(
        {"entries": [entry.to_dict()]}
    )
    assert registry.to_dict()["entry_count"] == 1


def test_signal_source_registry_helper_type_guards() -> None:
    with pytest.raises(TypeError, match="value must be a SignalSourceKind"):
        signal_registry._source_kind_code("attested_external")  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="value must be a SignalTrustTier"):
        signal_registry._trust_tier_code("verified")  # type: ignore[arg-type]


def test_signal_source_registry_rejects_missing_duplicate_and_bad_shapes() -> None:
    registry = _registry()
    missing = registry.validate(_trusted_external(source_id="oracle.missing"))
    assert missing.ok is False
    assert missing.error == "source_registry_entry_missing"

    with pytest.raises(ValueError, match="duplicate source registry entry: oracle.alpha"):
        ExternalSignalSourceRegistry(
            entries=(
                registry.entries[0],
                registry.entries[0],
            )
        )
    with pytest.raises(TypeError, match="source_id must be a string"):
        ExternalSignalSourceRegistryEntry(
            source_id=1,  # type: ignore[arg-type]
            source_kind=SignalSourceKind.ATTESTED_EXTERNAL,
            allowed_trust_tiers=(SignalTrustTier.VERIFIED,),
        )
    with pytest.raises(ValueError, match="source_id must be non-empty"):
        ExternalSignalSourceRegistryEntry(
            source_id="   ",
            source_kind=SignalSourceKind.ATTESTED_EXTERNAL,
            allowed_trust_tiers=(SignalTrustTier.VERIFIED,),
        )
    with pytest.raises(ValueError, match="source_id contains unsupported characters"):
        ExternalSignalSourceRegistryEntry(
            source_id="bad token!",
            source_kind=SignalSourceKind.ATTESTED_EXTERNAL,
            allowed_trust_tiers=(SignalTrustTier.VERIFIED,),
        )
    with pytest.raises(TypeError, match="source_kind must be a SignalSourceKind"):
        ExternalSignalSourceRegistryEntry(
            source_id="oracle.alpha",
            source_kind="attested_external",  # type: ignore[arg-type]
            allowed_trust_tiers=(SignalTrustTier.VERIFIED,),
        )
    with pytest.raises(TypeError, match="require_advisory_only must be a bool"):
        ExternalSignalSourceRegistryEntry(
            source_id="oracle.alpha",
            source_kind=SignalSourceKind.ATTESTED_EXTERNAL,
            allowed_trust_tiers=(SignalTrustTier.VERIFIED,),
            require_advisory_only=1,  # type: ignore[arg-type]
        )
    with pytest.raises(TypeError, match="require_auth must be a bool"):
        ExternalSignalSourceRegistryEntry(
            source_id="oracle.alpha",
            source_kind=SignalSourceKind.ATTESTED_EXTERNAL,
            allowed_trust_tiers=(SignalTrustTier.VERIFIED,),
            require_auth=1,  # type: ignore[arg-type]
        )
    with pytest.raises(TypeError, match="require_freshness must be a bool"):
        ExternalSignalSourceRegistryEntry(
            source_id="oracle.alpha",
            source_kind=SignalSourceKind.ATTESTED_EXTERNAL,
            allowed_trust_tiers=(SignalTrustTier.VERIFIED,),
            require_freshness=1,  # type: ignore[arg-type]
        )
    with pytest.raises(TypeError, match="enabled must be a bool"):
        ExternalSignalSourceRegistryEntry(
            source_id="oracle.alpha",
            source_kind=SignalSourceKind.ATTESTED_EXTERNAL,
            allowed_trust_tiers=(SignalTrustTier.VERIFIED,),
            enabled=1,  # type: ignore[arg-type]
        )
    with pytest.raises(
        TypeError,
        match="allowed_trust_tiers must contain SignalTrustTier members",
    ):
        ExternalSignalSourceRegistryEntry(
            source_id="oracle.alpha",
            source_kind=SignalSourceKind.ATTESTED_EXTERNAL,
            allowed_trust_tiers=("verified",),  # type: ignore[arg-type]
        )
    with pytest.raises(
        ValueError,
        match="allowed_trust_tiers must be non-empty when enabled",
    ):
        ExternalSignalSourceRegistryEntry(
            source_id="oracle.alpha",
            source_kind=SignalSourceKind.ATTESTED_EXTERNAL,
            allowed_trust_tiers=(),
            enabled=True,
        )
    with pytest.raises(TypeError, match="tags must be a string"):
        ExternalSignalSourceRegistryEntry(
            source_id="oracle.alpha",
            source_kind=SignalSourceKind.ATTESTED_EXTERNAL,
            allowed_trust_tiers=(SignalTrustTier.VERIFIED,),
            tags=(1,),  # type: ignore[arg-type]
        )
    with pytest.raises(
        TypeError,
        match="entries must contain ExternalSignalSourceRegistryEntry items",
    ):
        ExternalSignalSourceRegistry(entries=(object(),))  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="signal must be an ExternalSignalObservation"):
        registry.entries[0].validate(object())  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="signal must be an ExternalSignalObservation"):
        registry.validate(object())  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="external signal source registry entry must be an object"):
        external_signal_source_registry_entry_from_dict("bad")  # type: ignore[arg-type]
    with pytest.raises(
        TypeError,
        match="external signal source registry entry source_id must be a string",
    ):
        external_signal_source_registry_entry_from_dict(
            {
                "source_id": 1,
                "source_kind": "attested_external",
                "allowed_trust_tiers": ["verified"],
            }
        )
    with pytest.raises(
        TypeError,
        match="external signal source registry entry source_kind must be a string",
    ):
        external_signal_source_registry_entry_from_dict(
            {
                "source_id": "oracle.alpha",
                "source_kind": 1,
                "allowed_trust_tiers": ["verified"],
            }
        )
    with pytest.raises(
        TypeError,
        match="external signal source registry entry allowed_trust_tiers must be a list",
    ):
        external_signal_source_registry_entry_from_dict(
            {
                "source_id": "oracle.alpha",
                "source_kind": "attested_external",
                "allowed_trust_tiers": "verified",
            }
        )
    with pytest.raises(
        TypeError,
        match="external signal source registry entry tags must be a list",
    ):
        external_signal_source_registry_entry_from_dict(
            {
                "source_id": "oracle.alpha",
                "source_kind": "attested_external",
                "allowed_trust_tiers": ["verified"],
                "tags": "oracle",
            }
        )
    with pytest.raises(
        TypeError,
        match="external signal source registry entry require_auth must be a bool",
    ):
        external_signal_source_registry_entry_from_dict(
            {
                "source_id": "oracle.alpha",
                "source_kind": "attested_external",
                "allowed_trust_tiers": ["verified"],
                "require_auth": 1,
            }
        )
    with pytest.raises(
        ValueError,
        match="external signal source registry file must be a list or an object with entries",
    ):
        external_signal_source_registry_from_object("bad")
    singleton = external_signal_source_registry_from_object(
        {
            "source_id": "oracle.beta",
            "source_kind": "attested_external",
            "allowed_trust_tiers": ["verified"],
        }
    )
    assert singleton.get("oracle.beta") is not None


def test_signal_source_registry_enforces_entry_policy() -> None:
    registry = _registry(require_advisory_only=True)
    advisory_mode = registry.validate(_trusted_external(advisory_only=False))
    assert advisory_mode.ok is False
    assert advisory_mode.error == "source_registry_advisory_mode_required"

    auth = _advisory_registry().validate(_advisory_external(auth_ok=False))
    assert auth.ok is False
    assert auth.error == "source_registry_auth_required"

    freshness = _advisory_registry().validate(_advisory_external(freshness_ok=False))
    assert freshness.ok is False
    assert freshness.error == "source_registry_freshness_required"


def test_observation_packet_requires_registry_for_trusted_external_signals() -> None:
    pools, receipt = _market()
    primary = build_quote_receipt_signal_packet(receipt=receipt, pools_by_id=pools, current_epoch=5)
    with pytest.raises(ValueError, match="trusted external signals require a signal source registry"):
        build_autotrader_observation_packet(
            primary_signal=primary,
            external_signals=(_trusted_external(),),
        )

    packet = build_autotrader_observation_packet(
        primary_signal=primary,
        external_signals=(_trusted_external(),),
        signal_source_registry=_registry(),
    )
    encoded = packet.to_dict()
    assert encoded["signal_source_registry_present"] is True
    assert encoded["registered_external_count"] == 1

    with pytest.raises(
        TypeError,
        match="signal_source_registry must be an ExternalSignalSourceRegistry or None",
    ):
        build_autotrader_observation_packet(
            primary_signal=primary,
            external_signals=(_trusted_external(),),
            signal_source_registry=object(),  # type: ignore[arg-type]
        )

    with pytest.raises(
        ValueError,
        match="signal source registry rejected sig.oracle.1: source_registry_entry_missing",
    ):
        build_autotrader_observation_packet(
            primary_signal=primary,
            external_signals=(_trusted_external(),),
            signal_source_registry=ExternalSignalSourceRegistry(entries=()),
        )
