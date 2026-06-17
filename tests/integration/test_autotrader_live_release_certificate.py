from __future__ import annotations

from dataclasses import replace

import pytest

import src.integration.autotrader_live as autotrader_live
import src.integration.autotrader_live_release_certificate as live_release_certificate
from src.agents.policy_compiler import compile_policy_candidate
from src.agents.strategy_ir import AUTOTRADER_TAU_POLICY_SPECS, StrategyIR
from src.core.quote_receipts import make_route_quote_receipt
from src.core.routing import best_route_exact_in_2hop
from src.integration.autotrader_controller import (
    AutoTraderControllerState,
    AutoTraderDecision,
    AutoTraderDecisionTag,
    AutoTraderGuardState,
)
from src.integration.autotrader_live import (
    AutoTraderLiveReport,
    prepare_autotrader_live_quote_receipt,
)
from src.integration.autotrader_live_release_certificate import (
    build_autotrader_live_release_certificate,
    verify_autotrader_live_release_certificate,
    verify_autotrader_live_release_certificate_payload,
)
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey
from src.state.canonical import canonical_json_bytes, sha256_hex
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


def _single_hop_receipt(*, amount_in: int = 100, quote_epoch: int = 5) -> tuple[dict[str, PoolState], dict[str, object]]:
    pools = {"p_ab": _pool("p_ab", "A", "B", 1_000, 2_000, 10)}
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=amount_in)
    assert quote is not None
    receipt = make_route_quote_receipt(
        kind="exact_in",
        quote=quote,
        pools_by_id=pools,
        quote_epoch=quote_epoch,
    )
    return pools, receipt


def _compiled_strategy(
    *,
    owner_pubkey: str,
    backend: str = "local",
    fixed_order_size: int = 100,
) -> StrategyIR:
    return compile_policy_candidate(
        {
            "strategy_id": f"dca.{backend}.release",
            "owner_pubkey": owner_pubkey,
            "policy_backend": backend,
            "template": "dca",
            "asset_universe": ["A", "B"],
            "notional_caps": {
                "per_order_max": fixed_order_size,
                "per_window_max": 1_000,
                "lifetime_max": 10_000,
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
            "controls": {
                "kill_switch_enabled": True,
                "max_live_orders": 3,
            },
            "template_params": {
                "fixed_order_size": fixed_order_size,
                "cadence_epochs": 4,
                "asset_in": "A",
                "asset_out": "B",
            },
            "tau_policy_specs": list(AUTOTRADER_TAU_POLICY_SPECS) if backend == "tau" else [],
        }
    ).strategy


def test_build_live_release_certificate_for_successful_submit() -> None:
    privkey = 301
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        chain_id="tau-local",
        krr_backend="python",
        tx_sequence_number=9,
        tx_expiration_time=999,
    )

    certificate = build_autotrader_live_release_certificate(report)
    ok, err = verify_autotrader_live_release_certificate(report, certificate)

    assert report.decision.tag is AutoTraderDecisionTag.SUBMIT
    assert certificate.emit_requested is True
    assert certificate.live_admission_ok is True
    assert certificate.system_compose_ok is True
    assert certificate.submit_bundle_ok is True
    assert certificate.emit_finalize_ok is True
    assert certificate.release_ok is True
    assert certificate.release_error is None
    assert report.live_release_certificate == certificate
    assert report.live_release_certificate_error is None
    assert ok is True
    assert err is None
    assert certificate.release_hash_hex() == sha256_hex(canonical_json_bytes(certificate.to_unsigned_dict()))
    payload_ok, payload_err = verify_autotrader_live_release_certificate_payload(certificate.to_dict())
    assert payload_ok is True
    assert payload_err is None


def test_live_release_certificate_payload_verifier_rejects_malformed_payload() -> None:
    privkey = 301
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()
    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        chain_id="tau-local",
        krr_backend="python",
        tx_sequence_number=9,
        tx_expiration_time=999,
    )
    payload = build_autotrader_live_release_certificate(report).to_dict()
    payload["release_ok"] = "yes"
    unsigned_payload = {key: value for key, value in payload.items() if key != "release_hash"}
    payload["release_hash"] = sha256_hex(canonical_json_bytes(unsigned_payload))

    ok, err = verify_autotrader_live_release_certificate_payload(payload)

    assert ok is False
    assert err == "release_ok must be a bool"


def test_live_release_certificate_payload_verifier_does_not_swallow_adapter_bugs(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    privkey = 301
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()
    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        chain_id="tau-local",
        krr_backend="python",
        tx_sequence_number=9,
        tx_expiration_time=999,
    )
    payload = build_autotrader_live_release_certificate(report).to_dict()

    def broken_release_certificate_adapter(*_args: object, **_kwargs: object) -> object:
        raise RuntimeError("live release certificate adapter bug")

    monkeypatch.setattr(
        live_release_certificate,
        "AutoTraderLiveReleaseCertificate",
        broken_release_certificate_adapter,
    )
    with pytest.raises(RuntimeError, match="live release certificate adapter bug"):
        verify_autotrader_live_release_certificate_payload(payload)


def test_build_live_release_certificate_for_rejected_decision_binding(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    privkey = 302
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()
    original = autotrader_live.build_strategy_decision_certificate

    def _tampered(**kwargs: object):
        certificate = original(**kwargs)
        return replace(certificate, policy_artifact_hash="wrong.hash")

    monkeypatch.setattr(autotrader_live, "build_strategy_decision_certificate", _tampered)

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=privkey,
        last_used_nonce=0,
        chain_id="tau-local",
        krr_backend="python",
    )

    certificate = build_autotrader_live_release_certificate(report)
    ok, err = verify_autotrader_live_release_certificate(report, certificate)

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.live_admission_error == "decision_certificate_rejected:policy_artifact_hash mismatch"
    assert certificate.emit_requested is False
    assert certificate.release_ok is False
    assert certificate.release_error == "decision_certificate_rejected:policy_artifact_hash mismatch"
    assert report.live_release_certificate == certificate
    assert report.live_release_certificate_error is None
    assert ok is True
    assert err is None

    bad = replace(certificate, release_ok=True)
    ok, err = verify_autotrader_live_release_certificate(report, bad)
    assert ok is False
    assert err == "release_ok mismatch"

    payload = certificate.to_dict()
    payload["release_ok"] = True
    ok, err = verify_autotrader_live_release_certificate_payload(payload)
    assert ok is False
    assert err == "release_hash mismatch"


def test_build_live_release_certificate_rejects_incomplete_report() -> None:
    report = AutoTraderLiveReport(
        decision=AutoTraderDecision(
            tag=AutoTraderDecisionTag.REJECT,
            reason="missing",
            explain=("missing",),
            state=AutoTraderControllerState(),
            guard_state=AutoTraderGuardState(),
        ),
        signer_pubkey="0xabc",
        chain_id="tau-local",
        last_used_nonce_before=0,
        last_used_nonce_after=0,
    )

    with pytest.raises(ValueError, match="report.policy_artifact is required"):
        build_autotrader_live_release_certificate(report)
