from __future__ import annotations

from dataclasses import replace

import src.integration.autotrader_live as autotrader_live
from src.agents.policy_compiler import compile_policy_candidate
from src.agents.strategy_ir import AUTOTRADER_TAU_POLICY_SPECS, StrategyIR
from src.core.quote_receipts import make_route_quote_receipt
from src.core.routing import best_route_exact_in_2hop
from src.integration.autotrader_controller import AutoTraderControllerState, AutoTraderDecisionTag
from src.integration.autotrader_live import prepare_autotrader_live_quote_receipt
from src.integration.autotrader_stage_certificate import (
    build_autotrader_stage_certificate,
    verify_autotrader_stage_certificate,
    verify_autotrader_stage_certificate_payload,
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
            "strategy_id": f"dca.{backend}.stage",
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


def test_stage_certificate_attaches_to_successful_submit() -> None:
    privkey = 311
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
        tx_sequence_number=4,
        tx_expiration_time=999,
    )

    certificate = build_autotrader_stage_certificate(report)
    ok, err = verify_autotrader_stage_certificate(report, certificate)

    assert report.decision.tag is AutoTraderDecisionTag.SUBMIT
    assert report.stage_certificate == certificate
    assert report.stage_certificate_error is None
    assert certificate.highest_stage == "live_release"
    assert certificate.release_eligible is True
    assert certificate.blocker is None
    assert ok is True
    assert err is None
    assert certificate.stage_hash_hex() == sha256_hex(canonical_json_bytes(certificate.to_unsigned_dict()))
    payload_ok, payload_err = verify_autotrader_stage_certificate_payload(certificate.to_dict())
    assert payload_ok is True
    assert payload_err is None


def test_stage_certificate_attaches_to_signer_mismatch_reject() -> None:
    signer_privkey = 312
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(999)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()

    report = prepare_autotrader_live_quote_receipt(
        strategy=strategy,
        controller_state=AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        signer_privkey=signer_privkey,
        last_used_nonce=0,
        chain_id="tau-local",
        krr_backend="python",
    )

    certificate = build_autotrader_stage_certificate(report)
    ok, err = verify_autotrader_stage_certificate(report, certificate)

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.stage_certificate == certificate
    assert certificate.highest_stage == "signer"
    assert certificate.release_eligible is False
    assert certificate.blocker == "signer_pubkey_mismatch"
    assert certificate.tau_policy_bundle_hash is None
    assert ok is True
    assert err is None


def test_stage_certificate_tracks_policy_artifact_stage() -> None:
    privkey = 313
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _compiled_strategy(owner_pubkey=owner_pubkey)
    pools, receipt = _single_hop_receipt()
    compile_receipt = autotrader_live.build_compile_contract_tau_policy_receipt(strategy=strategy)
    bundle = autotrader_live.build_tau_policy_bundle(
        strategy=strategy,
        compile_contract_tau_receipt=compile_receipt.to_dict(),
    )
    unsigned_artifact = autotrader_live.build_strategy_policy_artifact(
        strategy=strategy,
        tau_policy_bundle=bundle,
    )

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
        tau_policy_bundle=bundle,
        policy_artifact=unsigned_artifact,
        krr_backend="python",
    )

    certificate = build_autotrader_stage_certificate(report)
    ok, err = verify_autotrader_stage_certificate(report, certificate)

    assert report.decision.tag is AutoTraderDecisionTag.REJECT
    assert report.stage_certificate == certificate
    assert certificate.highest_stage == "policy_artifact"
    assert certificate.release_eligible is False
    assert certificate.blocker == "signature_missing"
    assert certificate.tau_policy_bundle_hash is not None
    assert certificate.policy_artifact_hash is not None
    assert certificate.observation_hash is None
    assert ok is True
    assert err is None

    bad = replace(certificate, highest_stage="signer")
    ok, err = verify_autotrader_stage_certificate(report, bad)
    assert ok is False
    assert err == "highest_stage mismatch"

    payload = certificate.to_dict()
    payload["highest_stage"] = "signer"
    ok, err = verify_autotrader_stage_certificate_payload(payload)
    assert ok is False
    assert err == "stage_hash mismatch"
