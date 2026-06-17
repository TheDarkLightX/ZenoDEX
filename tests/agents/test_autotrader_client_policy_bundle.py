from __future__ import annotations

import json
from pathlib import Path

import pytest

import src.agents.autotrader_client_policy_bundle as client_policy_bundle
from src.agents.autotrader_client_policy_bundle import (
    AUTOTRADER_CLIENT_POLICY_BUNDLE_SCHEMA,
    autotrader_client_policy_bundle_from_dict,
    build_autotrader_client_policy_bundle,
    load_autotrader_client_policy_bundle_file,
    sign_autotrader_client_policy_bundle,
    verify_autotrader_client_policy_bundle_signature,
)
from src.agents.autotrader_client_policy_surface import build_autotrader_client_policy_surface
from src.agents.autotrader_local_guard_evaluator import (
    AutoTraderLocalGuardInputs,
    evaluate_autotrader_local_guards,
)
from src.agents.policy_artifacts import (
    build_strategy_policy_artifact,
    build_strategy_source_artifact,
    build_tau_policy_bundle,
    sign_strategy_policy_artifact,
)
from src.agents.strategy_ir import (
    AUTOTRADER_TAU_POLICY_SPECS,
    NotionalCaps,
    PolicyBackend,
    RiskLimits,
    StrategyAction,
    StrategyControls,
    StrategyIR,
    StrategyTemplate,
    StrategyWindow,
)
from src.agents.tau_policy_adapter import build_compile_contract_tau_policy_receipt
from src.integration.autotrader_signals import (
    QuoteReceiptSignalPacket,
    SignalSourceKind,
    SignalTrustTier,
)
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey


def _owner_pubkey(privkey: int = 21) -> str:
    return "0x" + bls_pubkey_hex_from_privkey(privkey)


def _strategy(*, strategy_id: str = "client.bundle.1", owner_privkey: int = 21) -> StrategyIR:
    return StrategyIR(
        strategy_id=strategy_id,
        owner_pubkey=_owner_pubkey(owner_privkey),
        policy_backend=PolicyBackend.TAU,
        template=StrategyTemplate.DCA,
        asset_universe=("BTC", "zUSD"),
        allowed_actions=(StrategyAction.PLACE_SWAP_EXACT_IN,),
        notional_caps=NotionalCaps(per_order_max=100, per_window_max=500, lifetime_max=1_000),
        risk_limits=RiskLimits(max_slippage_bps=75, max_oracle_staleness_epochs=3, require_quote_receipts=True),
        strategy_window=StrategyWindow(valid_from_epoch=10, valid_until_epoch=100, min_order_spacing_epochs=2),
        controls=StrategyControls(kill_switch_enabled=True, max_live_orders=3),
        template_params={"fixed_order_size": 100, "cadence_epochs": 4, "asset_in": "zUSD", "asset_out": "BTC"},
        tau_policy_specs=AUTOTRADER_TAU_POLICY_SPECS,
    )


def _packet(**overrides: object) -> QuoteReceiptSignalPacket:
    data = {
        "current_epoch": 12,
        "quote_epoch": 12,
        "asset_in": "zUSD",
        "asset_out": "BTC",
        "amount_in": 100,
        "amount_out": 181,
        "receipt_hash": "receipt.hash.bundle.1",
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


def _surface(strategy: StrategyIR, *, privkey: int = 21):
    source_artifact = build_strategy_source_artifact(strategy=strategy, source_form="kv")
    tau_policy_bundle = build_tau_policy_bundle(
        strategy=strategy,
        compile_contract_tau_receipt=build_compile_contract_tau_policy_receipt(strategy=strategy).to_dict(),
        source_artifact=source_artifact,
    )
    unsigned_policy_artifact = build_strategy_policy_artifact(
        strategy=strategy,
        tau_policy_bundle=tau_policy_bundle,
        source_artifact=source_artifact,
    )
    signed_policy_artifact = sign_strategy_policy_artifact(unsigned_policy_artifact, privkey=privkey)
    surface = build_autotrader_client_policy_surface(
        strategy=strategy,
        source_artifact=source_artifact,
        tau_policy_bundle=tau_policy_bundle,
        policy_artifact=signed_policy_artifact,
    )
    return surface, signed_policy_artifact


def test_client_policy_bundle_roundtrip_signature_and_guard_evaluation(tmp_path: Path) -> None:
    strategy = _strategy()
    surface, signed_policy_artifact = _surface(strategy)
    bundle = build_autotrader_client_policy_bundle(
        bundle_name="client.bundle.export.1",
        built_at="2026-04-09T15:20:00Z",
        client_policy_surface=surface,
        local_guard_inputs=AutoTraderLocalGuardInputs(
            current_epoch=12,
            order_amount=100,
            projected_live_orders=1,
            lifetime_spent=200,
            spent_in_window=100,
            budget_window_id=12,
            kill_switch_active=False,
            last_action_epoch=8,
            slippage_bps=50,
            signal_packet=_packet(),
        ),
    )

    assert bundle.to_dict()["schema"] == AUTOTRADER_CLIENT_POLICY_BUNDLE_SCHEMA
    assert bundle.local_guard_evaluation is not None
    assert bundle.local_guard_evaluation.ok is True
    assert bundle.client_policy_surface.policy_artifact_hash == signed_policy_artifact.policy_artifact_hash_hex()

    signed = sign_autotrader_client_policy_bundle(bundle, privkey=21)
    assert verify_autotrader_client_policy_bundle_signature(signed) is True

    path = tmp_path / "client_policy_bundle.json"
    path.write_text(json.dumps(signed.to_dict(), indent=2, sort_keys=True), encoding="utf-8")

    loaded = load_autotrader_client_policy_bundle_file(path)
    assert loaded.to_dict() == signed.to_dict()
    assert loaded.client_policy_bundle_hash_hex() == signed.client_policy_bundle_hash_hex()
    assert loaded.local_guard_evaluation is not None
    assert loaded.local_guard_evaluation.blocking_families == ()

    roundtrip = autotrader_client_policy_bundle_from_dict(signed.to_dict())
    assert roundtrip.to_dict() == signed.to_dict()


def test_client_policy_bundle_signature_propagates_unexpected_bls_backend_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class ExplodingBLS:
        @staticmethod
        def Verify(*_args: object) -> bool:
            raise RuntimeError("backend invariant failure")

    strategy = _strategy()
    surface, _signed_policy_artifact = _surface(strategy)
    bundle = sign_autotrader_client_policy_bundle(
        build_autotrader_client_policy_bundle(
            bundle_name="client.bundle.backend.failure",
            built_at="2026-04-09T15:20:00Z",
            client_policy_surface=surface,
        ),
        privkey=21,
    )
    monkeypatch.setattr(client_policy_bundle, "G2Basic", ExplodingBLS)

    with pytest.raises(RuntimeError, match="backend invariant failure"):
        verify_autotrader_client_policy_bundle_signature(bundle)


def test_client_policy_bundle_rejects_mismatched_guard_evaluation_strategy() -> None:
    strategy = _strategy(strategy_id="client.bundle.a")
    other_strategy = _strategy(strategy_id="client.bundle.b")
    surface, _ = _surface(strategy)
    evaluation = evaluate_autotrader_local_guards(
        strategy=other_strategy,
        inputs=AutoTraderLocalGuardInputs(
            current_epoch=12,
            order_amount=100,
            projected_live_orders=1,
            signal_packet=_packet(),
        ),
    )

    with pytest.raises(ValueError, match="strategy_id mismatch"):
        build_autotrader_client_policy_bundle(
            bundle_name="client.bundle.bad",
            built_at="2026-04-09T15:21:00Z",
            client_policy_surface=surface,
            local_guard_evaluation=evaluation,
        )


def test_client_policy_bundle_signing_rejects_non_owner_key() -> None:
    strategy = _strategy(owner_privkey=21)
    surface, _ = _surface(strategy, privkey=21)
    bundle = build_autotrader_client_policy_bundle(
        bundle_name="client.bundle.bad.signer",
        built_at="2026-04-09T15:22:00Z",
        client_policy_surface=surface,
    )

    with pytest.raises(ValueError, match="signer pubkey does not match client policy owner"):
        sign_autotrader_client_policy_bundle(bundle, privkey=22)


def test_client_policy_bundle_from_dict_rejects_bad_bundle_name_type() -> None:
    strategy = _strategy()
    surface, _ = _surface(strategy)
    bundle = sign_autotrader_client_policy_bundle(
        build_autotrader_client_policy_bundle(
            bundle_name="client.bundle.typed",
            built_at="2026-04-09T15:23:00Z",
            client_policy_surface=surface,
        ),
        privkey=21,
    )
    payload = bundle.to_dict()
    payload["bundle_name"] = 7

    with pytest.raises(TypeError, match="bundle_name must be a string"):
        autotrader_client_policy_bundle_from_dict(payload)
