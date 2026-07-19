from __future__ import annotations

from dataclasses import replace
from pathlib import Path

import pytest

from src.core.batch_clearing import compute_settlement
from src.core.liquidity import create_pool
from src.integration.operations import parse_intents
from src.integration.settlement_strong_certificate import (
    SettlementPriceHistoryCertificate,
    SettlementProofFlags,
    SettlementSemanticSummary,
    build_settlement_price_history_certificate,
    build_settlement_strong_certificate,
    derive_replay_bound_certificate_flags,
    derive_verified_replay_bound_certificate_flags,
    enforce_replay_bound_settlement_certificate,
    validate_settlement_strong_with_certificate,
    verify_settlement_strong_certificate,
)
from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps
from src.state import BalanceTable, LPTable
from src.state.intents import Intent, IntentKind

ROOT = Path(__file__).resolve().parents[2]


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _swap_context():
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(2200),
        sender_pubkey=pk,
        deadline=9_999_999_999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 1_000,
            "min_amount_out": 1,
        },
    )
    settlement = compute_settlement([intent], {pool_id: pool}, balances, LPTable())
    return intent, settlement, balances, {pool_id: pool}


def _four_swap_context():
    pk = "0x" + "22" * 48
    asset0 = "0x" + "03" * 32
    asset1 = "0x" + "04" * 32
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    balances = BalanceTable()
    balances.set(pk, asset0, 100_000)
    balances.set(pk, asset1, 0)
    intent_dicts = [
        {
            "module": "TauSwap",
            "version": "0.1",
            "kind": "SWAP_EXACT_IN",
            "intent_id": "0x" + f"{idx + 1:064x}",
            "sender_pubkey": pk,
            "deadline": 9_999_999_999,
            "nonce": idx + 1,
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 100,
            "min_amount_out": 1,
        }
        for idx in range(4)
    ]
    intents = parse_intents({"2": intent_dicts})
    settlement = compute_settlement(intents=intents, pools={pool_id: pool}, balances=balances, lp_balances=LPTable())
    return intents, settlement, balances, {pool_id: pool}


def test_build_and_verify_settlement_strong_certificate_round_trips() -> None:
    intent, settlement, balances, pools = _swap_context()
    flags = SettlementProofFlags.all_true()
    summary = SettlementSemanticSummary(a=1, b=2, c=3, d=4, price_pp=100, price_prev=110, price_curr=120)

    cert = build_settlement_strong_certificate(
        settlement=settlement,
        proof_flags=flags,
        semantic_summary=summary,
    )
    ok, err = verify_settlement_strong_certificate(settlement=settlement, certificate=cert)
    assert ok is True
    assert err is None
    assert cert.module_bundle_ok == 1
    assert cert.compact_bundle_ok == 1
    assert cert.full_price_rails_ok == 1
    assert cert.price_history_certificate is not None
    assert cert.price_history_certificate.price_trace_sha256

    ok, err = validate_settlement_strong_with_certificate(
        settlement=settlement,
        certificate=cert,
        intents=[intent],
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is True
    assert err is None


def test_verify_settlement_strong_certificate_rejects_tampered_settlement() -> None:
    _intent, settlement, _balances, _pools = _swap_context()
    cert = build_settlement_strong_certificate(settlement=settlement, proof_flags=SettlementProofFlags.all_true())

    first_delta = settlement.balance_deltas[0]
    tampered = replace(
        settlement,
        balance_deltas=[
            replace(first_delta, delta_sub=first_delta.delta_sub + 1),
            *settlement.balance_deltas[1:],
        ],
    )

    ok, err = verify_settlement_strong_certificate(settlement=tampered, certificate=cert)
    assert ok is False
    assert err == "settlement commitment mismatch"


def test_verify_settlement_strong_certificate_rejects_tampered_bundle_step() -> None:
    _intent, settlement, _balances, _pools = _swap_context()
    cert = build_settlement_strong_certificate(settlement=settlement, proof_flags=SettlementProofFlags.all_true())
    bad = replace(cert, module_bundle_step={"i1": 1, "i2": 1, "i3": 0})

    ok, err = verify_settlement_strong_certificate(settlement=settlement, certificate=bad)
    assert ok is False
    assert err == "module bundle step mismatch"


def test_verify_settlement_strong_certificate_rejects_tampered_spec_id() -> None:
    _intent, settlement, _balances, _pools = _swap_context()
    cert = build_settlement_strong_certificate(settlement=settlement, proof_flags=SettlementProofFlags.all_true())
    bad = replace(cert, compact_bundle_spec_id="wrong_spec")

    ok, err = verify_settlement_strong_certificate(settlement=settlement, certificate=bad)
    assert ok is False
    assert err == "compact bundle spec id mismatch"


def test_verify_settlement_strong_certificate_rejects_tampered_full_price_rails_spec_id() -> None:
    _intent, settlement, _balances, _pools = _swap_context()
    cert = build_settlement_strong_certificate(settlement=settlement, proof_flags=SettlementProofFlags.all_true())
    bad = replace(cert, full_price_rails_spec_id="wrong_spec")

    ok, err = verify_settlement_strong_certificate(settlement=settlement, certificate=bad)
    assert ok is False
    assert err == "full price rails spec id mismatch"


def test_verify_settlement_strong_certificate_rejects_tampered_price_history_packet() -> None:
    _intent, settlement, _balances, _pools = _swap_context()
    cert = build_settlement_strong_certificate(
        settlement=settlement,
        proof_flags=SettlementProofFlags.all_true(),
        semantic_summary=SettlementSemanticSummary(a=1, b=2, c=3, d=4, price_pp=100, price_prev=110, price_curr=120),
    )
    assert cert.price_history_certificate is not None
    bad_price_history = SettlementPriceHistoryCertificate(
        price_pp=cert.price_history_certificate.price_pp,
        price_prev=cert.price_history_certificate.price_prev,
        price_curr=cert.price_history_certificate.price_curr,
        price_trace_sha256="0" * 64,
    )
    bad = replace(cert, price_history_certificate=bad_price_history)

    ok, err = verify_settlement_strong_certificate(settlement=settlement, certificate=bad)
    assert ok is False
    assert err == "price history certificate mismatch"


def test_validate_settlement_strong_with_certificate_rejects_failed_module_bundle() -> None:
    intent, settlement, balances, pools = _swap_context()
    cert = build_settlement_strong_certificate(
        settlement=settlement,
        proof_flags=SettlementProofFlags(
            cpmm_ok=1,
            balance_ok=1,
            token_ok=1,
            buyback_floor_ok=1,
            buyback_floor_fixedpoint_ok=1,
            rebate_ok=1,
            lock_weight_ok=1,
            proof_ok=0,
            binding_ok=1,
        ),
    )

    ok, err = validate_settlement_strong_with_certificate(
        settlement=settlement,
        certificate=cert,
        intents=[intent],
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == "settlement certificate module bundle rejected"


def test_validate_settlement_strong_with_certificate_rejects_failed_full_price_rails() -> None:
    intent, settlement, balances, pools = _swap_context()
    cert = build_settlement_strong_certificate(
        settlement=settlement,
        proof_flags=SettlementProofFlags.all_true(),
        semantic_summary=SettlementSemanticSummary(a=1, b=2, c=3, d=4, price_pp=0, price_prev=60, price_curr=70),
    )
    assert cert.compact_bundle_ok == 1
    assert cert.full_price_rails_ok == 0

    ok, err = validate_settlement_strong_with_certificate(
        settlement=settlement,
        certificate=cert,
        intents=[intent],
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == "settlement certificate full price rails rejected"


def test_enforce_replay_bound_settlement_certificate_derives_core_flags_from_validator() -> None:
    intents, settlement, balances, pools = _four_swap_context()

    ok, err, cert = enforce_replay_bound_settlement_certificate(
        settlement=settlement,
        external_proof_flags=SettlementProofFlags(
            cpmm_ok=0,
            balance_ok=0,
            token_ok=0,
            buyback_floor_ok=1,
            buyback_floor_fixedpoint_ok=1,
            rebate_ok=1,
            lock_weight_ok=1,
            proof_ok=1,
            binding_ok=1,
        ),
        price_history=(100, 110, 120),
        intents=intents,
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )

    assert ok is True
    assert err is None
    assert cert is not None
    assert cert.proof_flags.cpmm_ok == 1
    assert cert.proof_flags.balance_ok == 1
    assert cert.proof_flags.token_ok == 1
    assert cert.price_history_certificate is not None
    assert cert.price_history_certificate.price_prev == 110
    assert cert.full_price_rails_ok == 1


def test_derive_replay_bound_certificate_flags_preserves_only_supplemental_lanes() -> None:
    flags = derive_replay_bound_certificate_flags(
        SettlementProofFlags(
            cpmm_ok=0,
            balance_ok=0,
            token_ok=0,
            buyback_floor_ok=1,
            buyback_floor_fixedpoint_ok=0,
            rebate_ok=1,
            lock_weight_ok=0,
            proof_ok=1,
            binding_ok=0,
        )
    )

    assert flags.cpmm_ok == 1
    assert flags.balance_ok == 1
    assert flags.token_ok == 1
    assert flags.buyback_floor_ok == 1
    assert flags.buyback_floor_fixedpoint_ok == 0
    assert flags.rebate_ok == 1
    assert flags.lock_weight_ok == 0
    assert flags.proof_ok == 1
    assert flags.binding_ok == 0


def test_derive_verified_replay_bound_certificate_flags_overrides_proof_binding_lanes() -> None:
    flags = derive_verified_replay_bound_certificate_flags(
        SettlementProofFlags(
            cpmm_ok=0,
            balance_ok=0,
            token_ok=0,
            buyback_floor_ok=1,
            buyback_floor_fixedpoint_ok=0,
            rebate_ok=1,
            lock_weight_ok=0,
            proof_ok=0,
            binding_ok=0,
        ),
        proof_ok=True,
        binding_ok=True,
    )

    assert flags.cpmm_ok == 1
    assert flags.balance_ok == 1
    assert flags.token_ok == 1
    assert flags.buyback_floor_ok == 1
    assert flags.buyback_floor_fixedpoint_ok == 0
    assert flags.rebate_ok == 1
    assert flags.lock_weight_ok == 0
    assert flags.proof_ok == 1
    assert flags.binding_ok == 1


def test_settlement_strong_certificate_tau_bundle_steps_replay() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    _intent, settlement, _balances, _pools = _swap_context()
    cert = build_settlement_strong_certificate(
        settlement=settlement,
        proof_flags=SettlementProofFlags.all_true(),
        semantic_summary=SettlementSemanticSummary(a=1, b=2, c=3, d=4, price_pp=100, price_prev=110, price_curr=120),
    )

    core = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=ROOT / "src" / "tau_specs" / "recommended" / "settlement_core_module_bundle_v1.tau",
        steps=[cert.core_module_step],
        timeout_s=60.0,
    )
    feature = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=ROOT / "src" / "tau_specs" / "recommended" / "settlement_feature_extension_bundle_v1.tau",
        steps=[cert.feature_extension_step],
        timeout_s=60.0,
    )
    proof = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=ROOT / "src" / "tau_specs" / "recommended" / "settlement_proof_binding_bundle_v1.tau",
        steps=[cert.proof_binding_step],
        timeout_s=60.0,
    )
    top = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=ROOT / "src" / "tau_specs" / "recommended" / "settlement_module_flag_bundle_v1.tau",
        steps=[cert.module_bundle_step],
        timeout_s=60.0,
    )
    compact = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=ROOT / "src" / "tau_specs" / "recommended" / "settlement_v5_aligned_compact_bundle.tau",
        steps=[cert.compact_bundle_step or {}],
        timeout_s=60.0,
    )
    rails = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=ROOT / "src" / "tau_specs" / "recommended" / "settlement_price_rails_aligned_v1.tau",
        steps=[cert.full_price_rails_step or {}],
        timeout_s=60.0,
    )

    assert core[0]["o1"] == cert.core_module_ok == 1
    assert feature[0]["o1"] == cert.feature_extension_ok == 1
    assert proof[0]["o1"] == cert.proof_binding_ok == 1
    assert top[0]["o1"] == cert.module_bundle_ok == 1
    assert compact[0]["o1"] == cert.compact_bundle_ok == 1
    assert rails[0]["o1"] == cert.full_price_rails_ok == 1


def test_build_settlement_price_history_certificate_hashes_canonical_trace() -> None:
    cert = build_settlement_price_history_certificate(price_pp=100, price_prev=110, price_curr=120)

    assert cert.schema == "zenodex/settlement-price-history-certificate/v1"
    assert cert.price_pp == 100
    assert cert.price_prev == 110
    assert cert.price_curr == 120
    assert len(cert.price_trace_sha256) == 64
