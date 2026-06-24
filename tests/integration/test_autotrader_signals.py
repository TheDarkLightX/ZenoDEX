from __future__ import annotations

import pytest

import src.integration.autotrader_signals as autotrader_signals
from src.agents.policy_compiler import compile_policy_candidate
from src.agents.strategy_ir import StrategyAction
from src.core.quote_receipts import make_route_quote_receipt
from src.core.routing import best_route_exact_in_2hop
from src.integration.autotrader_signals import (
    AutoTraderObservationPacket,
    AutoTraderSessionState,
    AutoTraderWalletCapability,
    ExternalSignalObservation,
    QuoteReceiptSignalPacket,
    SignalSourceKind,
    SignalTrustTier,
    _external_signal_source_kind_code,
    _external_signal_trust_tier_code,
    autotrader_observation_packet_from_dict,
    build_autotrader_observation_packet,
    build_quote_receipt_signal_packet,
    build_session_state_from_capability,
    build_wallet_capability_from_strategy,
    external_signal_observation_from_dict,
    external_signal_observations_from_object,
    quote_receipt_signal_packet_from_dict,
    verify_autotrader_observation_packet_payload,
    wallet_capability_from_dict,
)
from src.state.pools import PoolState, PoolStatus


def _pool(pid: str, a0: str, a1: str, r0: int, r1: int, fee_bps: int = 0) -> PoolState:
    return PoolState(
        pool_id=pid,
        asset0=min(a0, a1),
        asset1=max(a0, a1),
        reserve0=r0 if a0 < a1 else r1,
        reserve1=r1 if a0 < a1 else r0,
        fee_bps=fee_bps,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _market() -> tuple[dict[str, PoolState], dict[str, object]]:
    pools = {"p_ab": _pool("p_ab", "A", "B", 1_000, 2_000, 10)}
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=100)
    assert quote is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools, quote_epoch=5)
    return pools, receipt


def _strategy():
    return compile_policy_candidate(
        {
            "strategy_id": "signals.dca.1",
            "owner_pubkey": "owner.pubkey.1",
            "policy_backend": "local",
            "template": "dca",
            "asset_universe": ["A", "B"],
            "notional_caps": {
                "per_order_max": 100,
                "per_window_max": 500,
                "lifetime_max": 1_000,
            },
            "risk_limits": {
                "max_slippage_bps": 50,
                "max_oracle_staleness_epochs": 3,
            },
            "strategy_window": {
                "valid_from_epoch": 1,
                "valid_until_epoch": 100,
                "min_order_spacing_epochs": 0,
            },
            "template_params": {
                "fixed_order_size": 100,
                "cadence_epochs": 4,
                "asset_in": "A",
                "asset_out": "B",
            },
        }
    ).strategy


def test_build_quote_receipt_signal_packet_accepts_verified_receipt() -> None:
    pools, receipt = _market()
    packet = build_quote_receipt_signal_packet(receipt=receipt, pools_by_id=pools, current_epoch=5)
    assert packet.current_epoch == 5
    assert packet.quote_epoch == 5
    assert packet.source_kind is SignalSourceKind.ROUTE_QUOTE_RECEIPT
    assert packet.trust_tier is SignalTrustTier.VERIFIED
    assert packet.quote_receipt_verified is True
    assert packet.auth_ok is True
    assert packet.binding_ok is True
    assert packet.verify_error is None


def test_build_quote_receipt_signal_packet_captures_verification_failure() -> None:
    pools, receipt = _market()
    receipt = dict(receipt)
    receipt["receipt_hash"] = "bad.hash"
    packet = build_quote_receipt_signal_packet(receipt=receipt, pools_by_id=pools, current_epoch=5)
    assert packet.quote_receipt_present is True
    assert packet.quote_receipt_verified is False
    assert packet.auth_ok is False
    assert packet.binding_ok is False
    assert packet.verify_error is not None


def test_build_wallet_capability_from_strategy_tracks_remaining_budget() -> None:
    capability = build_wallet_capability_from_strategy(
        strategy=_strategy(),
        chain_id="tau-net-alpha",
        lifetime_spent=950,
        session_id="session.alpha",
    )
    assert capability.session_id == "session.alpha"
    assert capability.chain_id == "tau-net-alpha"
    assert capability.notional_remaining == 50
    assert capability.allowed_assets == ("A", "B")


def test_build_autotrader_observation_packet_summarizes_primary_and_external_signals() -> None:
    pools, receipt = _market()
    primary = build_quote_receipt_signal_packet(receipt=receipt, pools_by_id=pools, current_epoch=5)
    capability = build_wallet_capability_from_strategy(
        strategy=_strategy(),
        chain_id="tau-net-alpha",
    )
    packet = build_autotrader_observation_packet(
        primary_signal=primary,
        wallet_capability=capability,
        external_signals=(
            ExternalSignalObservation(
                signal_id="sig.news.1",
                source_id="newsfeed.alpha",
                source_kind=SignalSourceKind.ADVISORY_EXTERNAL,
                trust_tier=SignalTrustTier.ADVISORY,
                freshness_ok=True,
                auth_ok=False,
                tags=("macro", "macro"),
            ),
        ),
        tau_enabled=True,
    )

    encoded = packet.to_dict()
    assert encoded["schema"] == "zenodex/autotrader-observation-packet/v1"
    assert encoded["primary_signal"]["trust_tier"] == "verified"
    assert encoded["wallet_capability"]["chain_id"] == "tau-net-alpha"
    assert encoded["external_signals"][0]["tags"] == ["macro"]
    assert encoded["external_signal_count"] == 1
    assert encoded["advisory_external_count"] == 1
    assert encoded["trusted_external_count"] == 0
    assert encoded["signal_source_registry"] is None
    assert encoded["trusted_primary"] is True
    assert encoded["observation_packet_ok"] is True
    assert encoded["tau_enabled"] is True


def test_signal_wallet_and_observation_packets_roundtrip_with_payload_verifier() -> None:
    pools, receipt = _market()
    primary = build_quote_receipt_signal_packet(receipt=receipt, pools_by_id=pools, current_epoch=5)
    capability = build_wallet_capability_from_strategy(
        strategy=_strategy(),
        chain_id="tau-net-alpha",
        session_id="session.alpha",
    )
    packet = build_autotrader_observation_packet(
        primary_signal=primary,
        wallet_capability=capability,
        external_signals=(
            ExternalSignalObservation(
                signal_id="sig.news.2",
                source_id="feed.news.beta",
                source_kind=SignalSourceKind.ADVISORY_EXTERNAL,
                trust_tier=SignalTrustTier.ADVISORY,
                freshness_ok=True,
                auth_ok=False,
                advisory_only=True,
                tags=("macro",),
            ),
        ),
    )

    primary_payload = primary.to_dict()
    primary_roundtrip = quote_receipt_signal_packet_from_dict(primary_payload)
    assert primary_roundtrip == primary

    capability_payload = capability.to_dict()
    capability_roundtrip = wallet_capability_from_dict(capability_payload)
    assert capability_roundtrip == capability

    payload = packet.to_dict()
    roundtrip = autotrader_observation_packet_from_dict(payload)
    assert roundtrip == packet

    ok, error = verify_autotrader_observation_packet_payload(payload)
    assert ok is True
    assert error is None


def test_verify_autotrader_observation_packet_payload_rejects_tampered_summary() -> None:
    pools, receipt = _market()
    primary = build_quote_receipt_signal_packet(receipt=receipt, pools_by_id=pools, current_epoch=5)
    packet = build_autotrader_observation_packet(
        primary_signal=primary,
        external_signals=(
            ExternalSignalObservation(
                signal_id="sig.news.3",
                source_id="feed.news.gamma",
                source_kind=SignalSourceKind.ADVISORY_EXTERNAL,
                trust_tier=SignalTrustTier.ADVISORY,
                freshness_ok=True,
                auth_ok=False,
                advisory_only=True,
            ),
        ),
    )
    payload = packet.to_dict()
    payload["trusted_primary"] = False

    ok, error = verify_autotrader_observation_packet_payload(payload)
    assert ok is False
    assert error == "observation packet payload mismatch"


def test_verify_autotrader_observation_packet_payload_preserves_expected_validation_error(
    monkeypatch,
) -> None:
    def _bad_packet(_payload):
        raise ValueError("observation packet shape invalid")

    monkeypatch.setattr(
        autotrader_signals,
        "autotrader_observation_packet_from_dict",
        _bad_packet,
    )

    ok, error = verify_autotrader_observation_packet_payload({"schema": "bad"})

    assert ok is False
    assert error == "observation packet shape invalid"


def test_verify_autotrader_observation_packet_payload_sanitizes_unexpected_fault(
    monkeypatch,
) -> None:
    def _faulting_packet(_payload):
        raise RuntimeError("do not leak autotrader internals")

    monkeypatch.setattr(
        autotrader_signals,
        "autotrader_observation_packet_from_dict",
        _faulting_packet,
    )

    ok, error = verify_autotrader_observation_packet_payload({"schema": "bad"})

    assert ok is False
    assert error == "internal_error:RuntimeError"


@pytest.mark.parametrize(
    ("field", "value", "error_type", "message"),
    [
        ("source_kind", "route", TypeError, "source_kind must be a SignalSourceKind"),
        ("trust_tier", "verified", TypeError, "trust_tier must be a SignalTrustTier"),
        ("freshness_ok", 1, TypeError, "freshness_ok must be a bool"),
        ("auth_ok", 1, TypeError, "auth_ok must be a bool"),
        ("advisory_only", 1, TypeError, "advisory_only must be a bool"),
    ],
)
def test_external_signal_observation_rejects_invalid_fields(
    field: str,
    value: object,
    error_type: type[Exception],
    message: str,
) -> None:
    kwargs: dict[str, object] = {
        "signal_id": "sig.alpha",
        "source_id": "feed.alpha",
        "source_kind": SignalSourceKind.ADVISORY_EXTERNAL,
        "trust_tier": SignalTrustTier.ADVISORY,
        "freshness_ok": True,
        "auth_ok": False,
        "advisory_only": True,
    }
    kwargs[field] = value
    with pytest.raises(error_type, match=message):
        ExternalSignalObservation(**kwargs)


def test_external_signal_observation_rejects_bad_tokens() -> None:
    with pytest.raises(TypeError, match="signal_id must be a string"):
        ExternalSignalObservation(
            signal_id=123,
            source_id="feed.alpha",
            source_kind=SignalSourceKind.ADVISORY_EXTERNAL,
            trust_tier=SignalTrustTier.ADVISORY,
            freshness_ok=True,
            auth_ok=False,
        )
    with pytest.raises(ValueError, match="source_id must be non-empty"):
        ExternalSignalObservation(
            signal_id="sig.alpha",
            source_id="   ",
            source_kind=SignalSourceKind.ADVISORY_EXTERNAL,
            trust_tier=SignalTrustTier.ADVISORY,
            freshness_ok=True,
            auth_ok=False,
        )
    with pytest.raises(ValueError, match="tags contains unsupported characters"):
        ExternalSignalObservation(
            signal_id="sig.alpha",
            source_id="feed.alpha",
            source_kind=SignalSourceKind.ADVISORY_EXTERNAL,
            trust_tier=SignalTrustTier.ADVISORY,
            freshness_ok=True,
            auth_ok=False,
            tags=("bad space",),
        )


def test_external_signal_observation_accepts_advisory_and_attested_modes() -> None:
    advisory = ExternalSignalObservation(
        signal_id="sig.news.1",
        source_id="feed.news.alpha",
        source_kind=SignalSourceKind.ADVISORY_EXTERNAL,
        trust_tier=SignalTrustTier.ADVISORY,
        freshness_ok=False,
        auth_ok=False,
        advisory_only=True,
    )
    assert advisory.to_dict()["source_kind"] == "advisory_external"

    attested = ExternalSignalObservation(
        signal_id="sig.oracle.1",
        source_id="oracle.alpha",
        source_kind=SignalSourceKind.ATTESTED_EXTERNAL,
        trust_tier=SignalTrustTier.ATTESTED,
        freshness_ok=True,
        auth_ok=True,
        advisory_only=False,
    )
    assert attested.to_dict()["trust_tier"] == "attested"


def test_external_signal_code_helpers_cover_supported_and_fail_closed_cases() -> None:
    assert _external_signal_source_kind_code(SignalSourceKind.ADVISORY_EXTERNAL) == 1
    assert _external_signal_source_kind_code(SignalSourceKind.ATTESTED_EXTERNAL) == 2
    assert _external_signal_source_kind_code(SignalSourceKind.LOCAL_PROTOCOL_STATE) == 0
    assert _external_signal_trust_tier_code(SignalTrustTier.ADVISORY) == 0
    assert _external_signal_trust_tier_code(SignalTrustTier.ATTESTED) == 1
    assert _external_signal_trust_tier_code(SignalTrustTier.VERIFIED) == 2
    assert _external_signal_trust_tier_code(SignalTrustTier.PROTOCOL) == 0xFF
    with pytest.raises(TypeError, match="value must be a SignalSourceKind"):
        _external_signal_source_kind_code("bad")  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="value must be a SignalTrustTier"):
        _external_signal_trust_tier_code("bad")  # type: ignore[arg-type]


@pytest.mark.parametrize(
    ("kwargs", "match"),
    [
        (
            {
                "signal_id": "sig.news.bad",
                "source_id": "feed.news.alpha",
                "source_kind": SignalSourceKind.ADVISORY_EXTERNAL,
                "trust_tier": SignalTrustTier.ATTESTED,
                "freshness_ok": True,
                "auth_ok": True,
                "advisory_only": True,
            },
            "external signal contract rejected: advisory_external_invalid",
        ),
        (
            {
                "signal_id": "sig.oracle.bad",
                "source_id": "oracle.alpha",
                "source_kind": SignalSourceKind.ATTESTED_EXTERNAL,
                "trust_tier": SignalTrustTier.ADVISORY,
                "freshness_ok": True,
                "auth_ok": True,
                "advisory_only": False,
            },
            "external signal contract rejected: attested_external_invalid",
        ),
        (
            {
                "signal_id": "sig.oracle.bad2",
                "source_id": "oracle.alpha",
                "source_kind": SignalSourceKind.LOCAL_PROTOCOL_STATE,
                "trust_tier": SignalTrustTier.PROTOCOL,
                "freshness_ok": True,
                "auth_ok": True,
                "advisory_only": False,
            },
            "external signal contract rejected: source_kind_unsupported",
        ),
    ],
)
def test_external_signal_observation_rejects_invalid_contract_combinations(
    kwargs: dict[str, object],
    match: str,
) -> None:
    with pytest.raises(ValueError, match=match):
        ExternalSignalObservation(**kwargs)


def test_external_signal_observation_from_dict_and_collection_loader() -> None:
    advisory = external_signal_observation_from_dict(
        {
            "signal_id": "sig.news.1",
            "source_id": "feed.news.alpha",
            "source_kind": "advisory_external",
            "trust_tier": "advisory",
            "freshness_ok": True,
            "auth_ok": False,
            "advisory_only": True,
            "tags": ["macro", "macro"],
        }
    )
    assert advisory.tags == ("macro",)

    loaded = external_signal_observations_from_object(
        {
            "external_signals": [
                {
                    "signal_id": "sig.news.1",
                    "source_id": "feed.news.alpha",
                    "source_kind": "advisory_external",
                    "trust_tier": "advisory",
                    "freshness_ok": True,
                    "auth_ok": False,
                    "advisory_only": True,
                },
                {
                    "signal_id": "sig.oracle.1",
                    "source_id": "oracle.alpha",
                    "source_kind": "attested_external",
                    "trust_tier": "verified",
                    "freshness_ok": True,
                    "auth_ok": True,
                    "advisory_only": False,
                },
            ]
        }
    )
    assert len(loaded) == 2
    assert loaded[1].advisory_only is False
    assert loaded[1].trust_tier is SignalTrustTier.VERIFIED


def test_external_signal_collection_loader_accepts_none_and_single_object() -> None:
    assert external_signal_observations_from_object(None) == ()
    loaded = external_signal_observations_from_object(
        {
            "signal_id": "sig.news.2",
            "source_id": "feed.news.beta",
            "source_kind": "advisory_external",
            "trust_tier": "advisory",
            "freshness_ok": True,
            "auth_ok": False,
            "advisory_only": True,
        }
    )
    assert len(loaded) == 1
    assert loaded[0].signal_id == "sig.news.2"


@pytest.mark.parametrize(
    ("payload", "match"),
    [
        ("bad", "external signals file must be a list or an object with external_signals"),
        ({"external_signals": "bad"}, "external signals file must be a list or an object with external_signals"),
    ],
)
def test_external_signal_collection_loader_rejects_invalid_shapes(payload: object, match: str) -> None:
    with pytest.raises(ValueError, match=match):
        external_signal_observations_from_object(payload)


@pytest.mark.parametrize(
    ("payload", "error_type", "match"),
    [
        ("bad", TypeError, "external signal entry must be an object"),
        ({}, TypeError, "external signal signal_id must be a string"),
        ({"signal_id": "sig.1"}, TypeError, "external signal source_id must be a string"),
        (
            {"signal_id": "sig.1", "source_id": "feed.1"},
            TypeError,
            "external signal source_kind must be a string",
        ),
        (
            {"signal_id": "sig.1", "source_id": "feed.1", "source_kind": "advisory_external"},
            TypeError,
            "external signal trust_tier must be a string",
        ),
        (
            {
                "signal_id": "sig.1",
                "source_id": "feed.1",
                "source_kind": "advisory_external",
                "trust_tier": "advisory",
                "tags": "bad",
            },
            ValueError,
            "external signal tags must be a list",
        ),
    ],
)
def test_external_signal_observation_from_dict_rejects_invalid_shapes(
    payload: object,
    error_type: type[Exception],
    match: str,
) -> None:
    with pytest.raises(error_type, match=match):
        external_signal_observation_from_dict(payload)  # type: ignore[arg-type]


@pytest.mark.parametrize(
    ("field", "value", "error_type", "message"),
    [
        ("asset_out", "A", ValueError, "asset_in and asset_out must differ"),
        ("source_kind", "quote", TypeError, "source_kind must be a SignalSourceKind"),
        ("trust_tier", "verified", TypeError, "trust_tier must be a SignalTrustTier"),
        ("auth_ok", 1, TypeError, "auth_ok must be a bool"),
        ("verify_error", 1, TypeError, "verify_error must be a string or None"),
    ],
)
def test_quote_receipt_signal_packet_rejects_invalid_fields(
    field: str,
    value: object,
    error_type: type[Exception],
    message: str,
) -> None:
    kwargs: dict[str, object] = {
        "current_epoch": 5,
        "quote_epoch": 5,
        "asset_in": "A",
        "asset_out": "B",
        "amount_in": 100,
        "amount_out": 150,
        "receipt_hash": "hash.alpha",
    }
    kwargs[field] = value
    with pytest.raises(error_type, match=message):
        QuoteReceiptSignalPacket(**kwargs)


def test_quote_receipt_signal_packet_rejects_invalid_u32_inputs() -> None:
    with pytest.raises(TypeError, match="current_epoch must be an int"):
        QuoteReceiptSignalPacket(
            current_epoch=True,
            quote_epoch=5,
            asset_in="A",
            asset_out="B",
            amount_in=100,
            amount_out=150,
            receipt_hash="hash.alpha",
        )
    with pytest.raises(ValueError, match="quote_epoch out of u32 range"):
        QuoteReceiptSignalPacket(
            current_epoch=5,
            quote_epoch=-1,
            asset_in="A",
            asset_out="B",
            amount_in=100,
            amount_out=150,
            receipt_hash="hash.alpha",
        )


def test_wallet_capability_normalizes_duplicates_and_rejects_invalid_inputs() -> None:
    capability = AutoTraderWalletCapability(
        session_id="session.alpha",
        owner_pubkey="owner.pubkey.1",
        chain_id="tau-net-alpha",
        valid_from_epoch=1,
        valid_until_epoch=10,
        notional_remaining=50,
        allowed_assets=("A", "A", "B"),
        allowed_actions=(StrategyAction.PLACE_SWAP_EXACT_IN, StrategyAction.PLACE_SWAP_EXACT_IN),
    )
    assert capability.allowed_assets == ("A", "B")
    assert capability.allowed_actions == (StrategyAction.PLACE_SWAP_EXACT_IN,)

    with pytest.raises(ValueError, match="valid_from_epoch must be <= valid_until_epoch"):
        AutoTraderWalletCapability(
            session_id="session.alpha",
            owner_pubkey="owner.pubkey.1",
            chain_id="tau-net-alpha",
            valid_from_epoch=11,
            valid_until_epoch=10,
            notional_remaining=50,
            allowed_assets=("A",),
            allowed_actions=(StrategyAction.PLACE_SWAP_EXACT_IN,),
        )
    with pytest.raises(TypeError, match="enabled must be a bool"):
        AutoTraderWalletCapability(
            session_id="session.alpha",
            owner_pubkey="owner.pubkey.1",
            chain_id="tau-net-alpha",
            valid_from_epoch=1,
            valid_until_epoch=10,
            notional_remaining=50,
            allowed_assets=("A",),
            allowed_actions=(StrategyAction.PLACE_SWAP_EXACT_IN,),
            enabled=1,
        )
    with pytest.raises(ValueError, match="allowed_assets must be non-empty"):
        AutoTraderWalletCapability(
            session_id="session.alpha",
            owner_pubkey="owner.pubkey.1",
            chain_id="tau-net-alpha",
            valid_from_epoch=1,
            valid_until_epoch=10,
            notional_remaining=50,
            allowed_assets=(),
            allowed_actions=(StrategyAction.PLACE_SWAP_EXACT_IN,),
        )
    with pytest.raises(TypeError, match="allowed_actions must contain StrategyAction members"):
        AutoTraderWalletCapability(
            session_id="session.alpha",
            owner_pubkey="owner.pubkey.1",
            chain_id="tau-net-alpha",
            valid_from_epoch=1,
            valid_until_epoch=10,
            notional_remaining=50,
            allowed_assets=("A",),
            allowed_actions=("swap_exact_in",),
        )
    with pytest.raises(ValueError, match="allowed_actions must be non-empty"):
        AutoTraderWalletCapability(
            session_id="session.alpha",
            owner_pubkey="owner.pubkey.1",
            chain_id="tau-net-alpha",
            valid_from_epoch=1,
            valid_until_epoch=10,
            notional_remaining=50,
            allowed_assets=("A",),
            allowed_actions=(),
        )


def test_session_state_rejects_invalid_enabled_and_accepts_capability_builder() -> None:
    with pytest.raises(TypeError, match="enabled must be a bool"):
        AutoTraderSessionState(
            session_id="session.alpha",
            owner_pubkey="owner.pubkey.1",
            chain_id="tau-net-alpha",
            enabled=1,
        )

    strategy = _strategy()
    capability = build_wallet_capability_from_strategy(
        strategy=strategy,
        chain_id="tau-net-alpha",
        session_id="session.alpha",
    )
    session_state = build_session_state_from_capability(
        capability=capability,
        revoked_at_epoch=9,
        enabled=False,
    )
    assert session_state.session_id == capability.session_id
    assert session_state.owner_pubkey == capability.owner_pubkey
    assert session_state.chain_id == capability.chain_id
    assert session_state.enabled is False
    assert session_state.revoked_at_epoch == 9

    with pytest.raises(TypeError, match="capability must be an AutoTraderWalletCapability"):
        build_session_state_from_capability(capability=object())  # type: ignore[arg-type]


def test_observation_packet_normalizes_duplicates_and_rejects_invalid_inputs() -> None:
    pools, receipt = _market()
    primary = build_quote_receipt_signal_packet(receipt=receipt, pools_by_id=pools, current_epoch=5)
    external = ExternalSignalObservation(
        signal_id="sig.alpha",
        source_id="feed.alpha",
        source_kind=SignalSourceKind.ADVISORY_EXTERNAL,
        trust_tier=SignalTrustTier.ADVISORY,
        freshness_ok=True,
        auth_ok=False,
    )
    packet = AutoTraderObservationPacket(
        current_epoch=5,
        primary_signal=primary,
        external_signals=(external, external),
    )
    assert packet.external_signals == (external,)

    with pytest.raises(TypeError, match="primary_signal must be a QuoteReceiptSignalPacket"):
        AutoTraderObservationPacket(current_epoch=5, primary_signal=object())
    with pytest.raises(ValueError, match="primary_signal.current_epoch must equal current_epoch"):
        AutoTraderObservationPacket(
            current_epoch=6,
            primary_signal=primary,
        )
    with pytest.raises(TypeError, match="external_signals must contain ExternalSignalObservation items"):
        AutoTraderObservationPacket(
            current_epoch=5,
            primary_signal=primary,
            external_signals=(object(),),
        )
    with pytest.raises(TypeError, match="wallet_capability must be an AutoTraderWalletCapability or None"):
        AutoTraderObservationPacket(
            current_epoch=5,
            primary_signal=primary,
            wallet_capability=object(),
        )
    with pytest.raises(TypeError, match="tau_enabled must be a bool"):
        AutoTraderObservationPacket(
            current_epoch=5,
            primary_signal=primary,
            tau_enabled=1,
        )


def test_build_observation_packet_accepts_advisory_primary_but_rejects_ambiguous_external_mix() -> None:
    advisory_primary = QuoteReceiptSignalPacket(
        current_epoch=5,
        quote_epoch=5,
        asset_in="A",
        asset_out="B",
        amount_in=100,
        amount_out=150,
        receipt_hash="receipt.hash.advisory",
        source_kind=SignalSourceKind.ADVISORY_EXTERNAL,
        trust_tier=SignalTrustTier.ADVISORY,
        quote_receipt_present=True,
        quote_receipt_verified=True,
        quote_epoch_present=True,
        source_available=True,
        auth_ok=True,
        binding_ok=True,
    )
    packet = build_autotrader_observation_packet(primary_signal=advisory_primary)
    assert packet.trusted_primary() is False

    ambiguous = ExternalSignalObservation(
        signal_id="sig.oracle.advisory",
        source_id="oracle.alpha",
        source_kind=SignalSourceKind.ATTESTED_EXTERNAL,
        trust_tier=SignalTrustTier.VERIFIED,
        freshness_ok=True,
        auth_ok=True,
        advisory_only=True,
    )
    with pytest.raises(
        ValueError,
        match="observation packet contract rejected: external_signal_partition_invalid",
    ):
        build_autotrader_observation_packet(
            primary_signal=_primary_signal_for_contract_test(),
            external_signals=(ambiguous,),
        )


def _primary_signal_for_contract_test() -> QuoteReceiptSignalPacket:
    return QuoteReceiptSignalPacket(
        current_epoch=5,
        quote_epoch=5,
        asset_in="A",
        asset_out="B",
        amount_in=100,
        amount_out=150,
        receipt_hash="receipt.hash.primary",
        source_kind=SignalSourceKind.ROUTE_QUOTE_RECEIPT,
        trust_tier=SignalTrustTier.VERIFIED,
        quote_receipt_present=True,
        quote_receipt_verified=True,
        quote_epoch_present=True,
        source_available=True,
        auth_ok=True,
        binding_ok=True,
    )


def test_build_quote_receipt_signal_packet_rejects_invalid_inputs_and_missing_body() -> None:
    pools, receipt = _market()
    with pytest.raises(TypeError, match="receipt must be a mapping"):
        build_quote_receipt_signal_packet(receipt=[], pools_by_id=pools, current_epoch=5)
    with pytest.raises(TypeError, match="pools_by_id must be a mapping"):
        build_quote_receipt_signal_packet(receipt=receipt, pools_by_id=[], current_epoch=5)
    with pytest.raises(ValueError, match="missing receipt.body"):
        build_quote_receipt_signal_packet(
            receipt={"receipt_hash": "hash.alpha"},
            pools_by_id=pools,
            current_epoch=5,
        )


def test_build_quote_receipt_signal_packet_allows_missing_quote_epoch() -> None:
    pools, receipt = _market()
    body = dict(receipt["body"])
    body.pop("quote_epoch", None)
    receipt_without_epoch = dict(receipt)
    receipt_without_epoch["body"] = body
    packet = build_quote_receipt_signal_packet(
        receipt=receipt_without_epoch,
        pools_by_id=pools,
        current_epoch=5,
    )
    assert packet.quote_epoch_present is False
    assert packet.quote_epoch == 0


def test_build_wallet_capability_from_strategy_rejects_invalid_strategy_and_clamps_below_zero() -> None:
    with pytest.raises(TypeError, match="strategy must be a StrategyIR"):
        build_wallet_capability_from_strategy(strategy=object(), chain_id="tau-net-alpha")

    capability = build_wallet_capability_from_strategy(
        strategy=_strategy(),
        chain_id="tau-net-alpha",
        lifetime_spent=2_000,
    )
    assert capability.notional_remaining == 0
