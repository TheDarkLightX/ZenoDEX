from __future__ import annotations

from src.integration.decision_witness import (
    build_decision_witness_from_autotrader_binary_decision,
    build_decision_witness_from_autotrader_multiaction_decision,
    build_decision_witness_from_exact_in_true_key_interpretation_packet,
    build_decision_witness_from_exact_out_repaired_key_cover_interpretation_packet,
    build_decision_witness_from_settlement_end_to_end_certificate_packet,
    verify_decision_witness_against_autotrader_binary_decision,
    verify_decision_witness_against_autotrader_multiaction_decision,
    verify_decision_witness_against_exact_in_true_key_interpretation_packet,
    verify_decision_witness_against_exact_out_repaired_key_cover_interpretation_packet,
    verify_decision_witness_against_settlement_end_to_end_certificate_packet,
)
from src.agents.policy_artifacts import build_strategy_policy_artifact, build_tau_policy_bundle
from src.agents.strategy_ir import (
    NotionalCaps,
    PolicyBackend,
    RiskLimits,
    StrategyAction,
    StrategyIR,
    StrategyTemplate,
    StrategyWindow,
)
from src.agents.tau_policy_adapter import build_compile_contract_tau_policy_receipt
from src.integration.autotrader_decision import (
    build_strategy_candidate_set,
    build_strategy_decision_certificate,
)
from src.integration.autotrader_multiaction_decision import (
    build_bounded_multi_action_candidate_set,
    build_bounded_multi_action_decision_certificate,
)
from src.integration.autotrader_signals import (
    AutoTraderObservationPacket,
    AutoTraderWalletCapability,
    QuoteReceiptSignalPacket,
)
from src.integration.exact_in_route_certificate import (
    build_exact_in_route_true_key_interpretation_packet,
)
from src.integration.exact_out_route_certificate import (
    build_exact_out_many_pool_repaired_key_cover_interpretation_packet,
)
from src.integration.settlement_end_to_end_certificate_packet import (
    build_settlement_end_to_end_certificate_packet_from_price_packet,
)
from src.integration.settlement_feature_extension_packet import SettlementFeatureExtensionInputs
from src.integration.settlement_price_provenance import (
    SettlementSpotPriceEntry,
    build_settlement_spot_price_packet,
)
from src.integration.settlement_strong_certificate import SettlementProofFlags
from src.core.routing import RouteHop, RouteLeg, RouteQuote
from src.core.batch_clearing import compute_settlement
from src.core.liquidity import create_pool
from src.state import BalanceTable, LPTable
from src.state.intents import Intent, IntentKind
from src.state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus


def _autotrader_strategy(*, multi_action: bool = False) -> StrategyIR:
    allowed_actions = (
        (
            StrategyAction.PLACE_SWAP_EXACT_IN,
            StrategyAction.PLACE_SWAP_EXACT_OUT,
            StrategyAction.PLACE_ORDER_INTENT,
        )
        if multi_action
        else (StrategyAction.PLACE_SWAP_EXACT_IN,)
    )
    return StrategyIR(
        strategy_id="decision-witness.autotrader.1",
        owner_pubkey="owner.pubkey.1",
        policy_backend=PolicyBackend.LOCAL,
        template=StrategyTemplate.DCA,
        asset_universe=("BTC", "zUSD"),
        allowed_actions=allowed_actions,
        notional_caps=NotionalCaps(per_order_max=100, per_window_max=500, lifetime_max=1_000),
        risk_limits=RiskLimits(max_slippage_bps=50, max_oracle_staleness_epochs=3),
        strategy_window=StrategyWindow(valid_from_epoch=1, valid_until_epoch=100),
        template_params={
            "fixed_order_size": 100,
            "cadence_epochs": 4,
            "asset_in": "zUSD",
            "asset_out": "BTC",
        },
    )


def _autotrader_packet(*, multi_action: bool = False) -> AutoTraderObservationPacket:
    allowed_actions = (
        (
            StrategyAction.PLACE_SWAP_EXACT_IN,
            StrategyAction.PLACE_SWAP_EXACT_OUT,
            StrategyAction.PLACE_ORDER_INTENT,
        )
        if multi_action
        else (StrategyAction.PLACE_SWAP_EXACT_IN,)
    )
    return AutoTraderObservationPacket(
        current_epoch=10,
        primary_signal=QuoteReceiptSignalPacket(
            current_epoch=10,
            quote_epoch=9,
            asset_in="zUSD",
            asset_out="BTC",
            amount_in=100,
            amount_out=95,
            receipt_hash="receipt.hash.decision-witness.1",
        ),
        wallet_capability=AutoTraderWalletCapability(
            session_id="session.1",
            owner_pubkey="owner.pubkey.1",
            chain_id="tau-net-alpha",
            valid_from_epoch=1,
            valid_until_epoch=100,
            notional_remaining=500,
            allowed_assets=("BTC", "zUSD"),
            allowed_actions=allowed_actions,
        ),
        tau_enabled=False,
    )


def _autotrader_artifact_bundle(
    *,
    multi_action: bool = False,
) -> tuple[StrategyIR, AutoTraderObservationPacket, object, object]:
    strategy = _autotrader_strategy(multi_action=multi_action)
    packet = _autotrader_packet(multi_action=multi_action)
    bundle = build_tau_policy_bundle(
        strategy=strategy,
        compile_contract_tau_receipt=build_compile_contract_tau_policy_receipt(strategy=strategy).to_dict(),
    )
    artifact = build_strategy_policy_artifact(strategy=strategy, tau_policy_bundle=bundle)
    return strategy, packet, artifact, bundle


def _quote_one_hop(*, pool_id: str, amount_in: int = 10, amount_out: int = 11) -> RouteQuote:
    hop = RouteHop(
        pool_id=pool_id,
        asset_in="A",
        asset_out="B",
        amount_in=amount_in,
        amount_out=amount_out,
    )
    leg = RouteLeg(hops=(hop,), amount_in=amount_in, amount_out=amount_out)
    return RouteQuote(asset_in="A", asset_out="B", amount_in=amount_in, amount_out=amount_out, legs=(leg,))


def _quote_two_hop(
    *,
    pool0: str,
    pool1: str,
    intermediate_asset: str,
    amount_in: int = 10,
    amount_mid: int = 12,
    amount_out: int = 15,
) -> RouteQuote:
    hop0 = RouteHop(
        pool_id=pool0,
        asset_in="A",
        asset_out=intermediate_asset,
        amount_in=amount_in,
        amount_out=amount_mid,
    )
    hop1 = RouteHop(
        pool_id=pool1,
        asset_in=intermediate_asset,
        asset_out="B",
        amount_in=amount_mid,
        amount_out=amount_out,
    )
    leg = RouteLeg(hops=(hop0, hop1), amount_in=amount_in, amount_out=amount_out)
    return RouteQuote(asset_in="A", asset_out="B", amount_in=amount_in, amount_out=amount_out, legs=(leg,))


def _pool(*, pool_id: str, reserve0: int, reserve1: int) -> PoolState:
    return PoolState(
        pool_id=pool_id,
        asset0="A",
        asset1="B",
        reserve0=int(reserve0),
        reserve1=int(reserve1),
        fee_bps=0,
        lp_supply=1_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
        curve_tag=CURVE_TAG_CPMM,
    )


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _four_swap_settlement_context():
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
    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(idx + 1),
            sender_pubkey=pk,
            deadline=9_999_999_999,
            fields={
                "pool_id": pool_id,
                "asset_in": asset0,
                "asset_out": asset1,
                "amount_in": 100,
                "min_amount_out": 1,
            },
        )
        for idx in range(4)
    ]
    settlement = compute_settlement(intents, {pool_id: pool}, balances, LPTable())
    price_packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset=asset0, price=100, observed_epoch=95, age_epochs=5, source_id="oracle:a"),
            SettlementSpotPriceEntry(asset=asset1, price=120, observed_epoch=97, age_epochs=3, source_id="oracle:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )
    packet = build_settlement_end_to_end_certificate_packet_from_price_packet(
        settlement=settlement,
        proof_flags=SettlementProofFlags.all_true(),
        price_history=(100, 110, 120),
        feature_extension_inputs=SettlementFeatureExtensionInputs(
            trade_amount=100,
            fee_charged=1,
            buyback_amount=1,
            burned_amount=1,
            supply_before=1_000,
            supply_after=999,
            supply_floor=500,
            unit_scale=1,
            rebate_rate_bps=500,
            rebate_amount=1,
            rebate_cap=1,
            lock_days=60,
            stake_amount=50,
            tier1_days=30,
            tier2_days=90,
            weight_t1=1,
            weight_t2=2,
            weight_t3=3,
            weight_claimed=2,
            weighted_stake=100,
        ),
        price_packet=price_packet,
    )
    return settlement, packet


def test_exact_in_true_key_packet_adapts_into_decision_witness() -> None:
    packet = build_exact_in_route_true_key_interpretation_packet(
        [
            _quote_two_hop(pool0="p_b", pool1="p_c", intermediate_asset="C", amount_out=13),
            _quote_one_hop(pool_id="p_a", amount_out=14),
            _quote_one_hop(pool_id="p_b", amount_out=14),
        ]
    )

    witness = build_decision_witness_from_exact_in_true_key_interpretation_packet(packet)

    assert witness.witness_kind == "exact_in_route"
    assert witness.state_binding.binding_kind == "exact_in_candidate_set"
    assert witness.request_binding.binding_id == "A->B:10"
    assert witness.canonical_key[0] == -14
    assert witness.feasibility_payload["winner_true_key_minimal"] is True
    assert witness.proof_payload is not None
    assert witness.proof_payload["packet_ok"] is True

    ok, err = verify_decision_witness_against_exact_in_true_key_interpretation_packet(
        packet, witness.to_dict()
    )
    assert ok, err


def test_exact_in_true_key_packet_witness_checker_rejects_tampering() -> None:
    packet = build_exact_in_route_true_key_interpretation_packet(
        [
            _quote_two_hop(pool0="p_b", pool1="p_c", intermediate_asset="C", amount_out=13),
            _quote_one_hop(pool_id="p_a", amount_out=14),
            _quote_one_hop(pool_id="p_b", amount_out=14),
        ]
    )
    payload = build_decision_witness_from_exact_in_true_key_interpretation_packet(packet).to_dict()
    payload["canonical_key"][0] = -13

    ok, err = verify_decision_witness_against_exact_in_true_key_interpretation_packet(packet, payload)
    assert not ok
    assert err == "decision witness payload mismatch for exact-in packet"


def test_exact_out_repaired_key_cover_packet_adapts_into_decision_witness() -> None:
    packet = build_exact_out_many_pool_repaired_key_cover_interpretation_packet(
        (
            _pool(pool_id="p0", reserve0=20, reserve1=10),
            _pool(pool_id="p1", reserve0=20, reserve1=10),
            _pool(pool_id="p2", reserve0=30, reserve1=15),
            _pool(pool_id="p3", reserve0=30, reserve1=15),
        ),
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )

    witness = build_decision_witness_from_exact_out_repaired_key_cover_interpretation_packet(packet)

    assert witness.witness_kind == "exact_out_route"
    assert witness.state_binding.binding_kind == "exact_out_repaired_audit_domain"
    assert witness.request_binding.binding_id == "A->B:4"
    assert witness.feasibility_payload["selected_domain_canonical_matches_full_domain_canonical"] is True
    assert witness.proof_payload is not None
    assert witness.proof_payload["packet_ok"] is True
    assert witness.accounting_receipt is not None
    assert witness.accounting_receipt["selected_domain_runtime_matches_full_domain_canonical"] is True

    ok, err = verify_decision_witness_against_exact_out_repaired_key_cover_interpretation_packet(
        packet, witness.to_dict()
    )
    assert ok, err


def test_exact_out_repaired_key_cover_witness_checker_rejects_tampering() -> None:
    packet = build_exact_out_many_pool_repaired_key_cover_interpretation_packet(
        (
            _pool(pool_id="p0", reserve0=20, reserve1=10),
            _pool(pool_id="p1", reserve0=20, reserve1=10),
            _pool(pool_id="p2", reserve0=30, reserve1=15),
            _pool(pool_id="p3", reserve0=30, reserve1=15),
        ),
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )
    payload = build_decision_witness_from_exact_out_repaired_key_cover_interpretation_packet(packet).to_dict()
    payload["feasibility_payload"]["domination_witnesses_dominate"] = False

    ok, err = verify_decision_witness_against_exact_out_repaired_key_cover_interpretation_packet(
        packet, payload
    )
    assert not ok
    assert err == "decision witness payload mismatch for exact-out packet"


def test_settlement_end_to_end_packet_adapts_into_decision_witness() -> None:
    settlement, packet = _four_swap_settlement_context()

    witness = build_decision_witness_from_settlement_end_to_end_certificate_packet(
        settlement=settlement,
        packet=packet,
    )

    assert witness.witness_kind == "settlement_step"
    assert witness.state_binding.binding_kind == "settlement_certificate_boundary"
    assert witness.request_binding.binding_kind == "settlement_request"
    assert witness.quote_binding is not None
    assert witness.quote_binding.binding_kind == "settlement_price_packet"
    assert witness.epoch_binding is not None
    assert witness.epoch_binding.binding_kind == "settlement_price_epoch"
    assert witness.feasibility_payload["full_price_rails_ok"] is True
    assert witness.feasibility_payload["settlement_commitment_matches"] is True
    assert witness.feasibility_payload["delta_commitment_matches"] is True
    assert witness.accounting_receipt is not None
    assert witness.accounting_receipt["full_price_rails_ok"] is True
    assert witness.accounting_receipt["balance_deltas"]
    assert witness.accounting_receipt["reserve_deltas"]
    assert witness.accounting_receipt["value_lane_result"]["schema"] == packet.value_packet.schema

    ok, err = verify_decision_witness_against_settlement_end_to_end_certificate_packet(
        settlement=settlement,
        packet=packet,
        witness_payload=witness.to_dict(),
    )
    assert ok, err


def test_settlement_end_to_end_packet_witness_checker_rejects_tampering() -> None:
    settlement, packet = _four_swap_settlement_context()
    payload = build_decision_witness_from_settlement_end_to_end_certificate_packet(
        settlement=settlement,
        packet=packet,
    ).to_dict()
    payload["accounting_receipt"]["full_price_rails_ok"] = False

    ok, err = verify_decision_witness_against_settlement_end_to_end_certificate_packet(
        settlement=settlement,
        packet=packet,
        witness_payload=payload,
    )
    assert not ok
    assert err == "decision witness payload mismatch for settlement packet"


def test_autotrader_binary_decision_adapts_into_decision_witness() -> None:
    strategy, packet, artifact, bundle = _autotrader_artifact_bundle()
    candidate_set = build_strategy_candidate_set(
        policy_artifact=artifact,
        tau_policy_bundle=bundle,
        observation_packet=packet,
        emit_requested=True,
        emit_admissible=True,
    )
    certificate = build_strategy_decision_certificate(
        candidate_set=candidate_set,
        kill_switch_active=False,
    )

    witness = build_decision_witness_from_autotrader_binary_decision(
        strategy=strategy,
        observation_packet=packet,
        candidate_set=candidate_set,
        certificate=certificate,
    )

    assert witness.witness_kind == "autotrader_binary_decision"
    assert witness.state_binding.binding_kind == "autotrader_binary_candidate_set"
    assert witness.request_binding.binding_kind == "autotrader_strategy"
    assert witness.quote_binding is not None
    assert witness.quote_binding.binding_kind == "autotrader_observation_packet"
    assert witness.epoch_binding is not None
    assert witness.epoch_binding.binding_id == "10"
    assert witness.expires_at == 100
    assert witness.feasibility_payload["binding_ok"] is True
    assert witness.feasibility_payload["winner_kind"] == "emit_compiled_intent"
    assert witness.canonical_key[0] == -1
    assert witness.accounting_receipt is not None
    assert witness.accounting_receipt["amount_out"] == 95
    assert witness.proof_payload is not None
    assert witness.proof_payload["binding_ok"] is True

    ok, err = verify_decision_witness_against_autotrader_binary_decision(
        strategy=strategy,
        observation_packet=packet,
        candidate_set=candidate_set,
        certificate=certificate,
        witness_payload=witness.to_dict(),
    )
    assert ok, err


def test_autotrader_binary_decision_witness_checker_rejects_tampering() -> None:
    strategy, packet, artifact, bundle = _autotrader_artifact_bundle()
    candidate_set = build_strategy_candidate_set(
        policy_artifact=artifact,
        tau_policy_bundle=bundle,
        observation_packet=packet,
        emit_requested=True,
        emit_admissible=True,
    )
    certificate = build_strategy_decision_certificate(
        candidate_set=candidate_set,
        kill_switch_active=False,
    )
    payload = build_decision_witness_from_autotrader_binary_decision(
        strategy=strategy,
        observation_packet=packet,
        candidate_set=candidate_set,
        certificate=certificate,
    ).to_dict()
    payload["feasibility_payload"]["binding_ok"] = False

    ok, err = verify_decision_witness_against_autotrader_binary_decision(
        strategy=strategy,
        observation_packet=packet,
        candidate_set=candidate_set,
        certificate=certificate,
        witness_payload=payload,
    )
    assert not ok
    assert err == "decision witness payload mismatch for autotrader binary decision"


def test_autotrader_multiaction_decision_adapts_into_decision_witness() -> None:
    strategy, packet, artifact, bundle = _autotrader_artifact_bundle(multi_action=True)
    candidate_set = build_bounded_multi_action_candidate_set(
        policy_artifact=artifact,
        tau_policy_bundle=bundle,
        observation_packet=packet,
        action_frontier={
            StrategyAction.PLACE_SWAP_EXACT_IN: (True, True, 10),
            StrategyAction.PLACE_SWAP_EXACT_OUT: (True, True, 30),
            StrategyAction.PLACE_ORDER_INTENT: (True, False, 40),
        },
    )
    certificate = build_bounded_multi_action_decision_certificate(candidate_set=candidate_set)

    witness = build_decision_witness_from_autotrader_multiaction_decision(
        strategy=strategy,
        observation_packet=packet,
        candidate_set=candidate_set,
        certificate=certificate,
    )

    assert witness.witness_kind == "autotrader_multiaction_decision"
    assert witness.state_binding.binding_kind == "autotrader_multiaction_candidate_set"
    assert witness.request_binding.binding_kind == "autotrader_strategy"
    assert witness.feasibility_payload["binding_ok"] is True
    assert witness.feasibility_payload["winner_kind"] == "place_swap_exact_out"
    assert witness.feasibility_payload["frontier_width"] == 4
    assert witness.canonical_key[0] < 0
    assert witness.accounting_receipt is not None
    assert witness.accounting_receipt["amount_in"] == 100
    assert witness.proof_payload is not None
    assert witness.proof_payload["frontier_width"] == 4

    ok, err = verify_decision_witness_against_autotrader_multiaction_decision(
        strategy=strategy,
        observation_packet=packet,
        candidate_set=candidate_set,
        certificate=certificate,
        witness_payload=witness.to_dict(),
    )
    assert ok, err


def test_autotrader_multiaction_decision_witness_checker_rejects_tampering() -> None:
    strategy, packet, artifact, bundle = _autotrader_artifact_bundle(multi_action=True)
    candidate_set = build_bounded_multi_action_candidate_set(
        policy_artifact=artifact,
        tau_policy_bundle=bundle,
        observation_packet=packet,
        action_frontier={
            StrategyAction.PLACE_SWAP_EXACT_IN: (True, True, 10),
            StrategyAction.PLACE_SWAP_EXACT_OUT: (True, True, 30),
            StrategyAction.PLACE_ORDER_INTENT: (True, False, 40),
        },
    )
    certificate = build_bounded_multi_action_decision_certificate(candidate_set=candidate_set)
    payload = build_decision_witness_from_autotrader_multiaction_decision(
        strategy=strategy,
        observation_packet=packet,
        candidate_set=candidate_set,
        certificate=certificate,
    ).to_dict()
    payload["canonical_key"][1] = 999

    ok, err = verify_decision_witness_against_autotrader_multiaction_decision(
        strategy=strategy,
        observation_packet=packet,
        candidate_set=candidate_set,
        certificate=certificate,
        witness_payload=payload,
    )
    assert not ok
    assert err == "decision witness payload mismatch for autotrader multi-action decision"
