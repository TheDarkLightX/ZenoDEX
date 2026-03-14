from __future__ import annotations

from src.agents.krr_policy_advisor import (
    _load_history_check_rows,
    _load_source_history_rows,
    _merge_autotrader_krr_defaults,
    _merge_list,
    _merge_named_rules,
    _source_quality_summary,
    advise_autotrader_krr,
    autotrader_krr_check_options,
    autotrader_krr_semantic_signature,
)
from src.agents.policy_compiler import compile_policy_candidate
from src.agents.strategy_ir import strategy_ir_from_dict
from src.core.quote_receipts import make_route_quote_receipt
from src.core.routing import best_route_exact_in_2hop
from src.integration.autotrader_signal_registry import (
    ExternalSignalSourceRegistry,
    ExternalSignalSourceRegistryEntry,
)
from src.integration.autotrader_signals import (
    ExternalSignalObservation,
    QuoteReceiptSignalPacket,
    SignalSourceKind,
    SignalTrustTier,
    build_autotrader_observation_packet,
    build_quote_receipt_signal_packet,
)
from src.state.pools import PoolState, PoolStatus


def _strategy(*, backend: str = "local", fixed_order_size: int = 100):
    candidate: dict[str, object] = {
        "strategy_id": f"dca.{backend}.krr",
        "owner_pubkey": "owner.pubkey.1",
        "policy_backend": backend,
        "template": "dca",
        "asset_universe": ["A", "B"],
        "notional_caps": {
            "per_order_max": fixed_order_size,
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
        "controls": {
            "kill_switch_enabled": True,
            "max_live_orders": 2,
        },
        "template_params": {
            "fixed_order_size": fixed_order_size,
            "cadence_epochs": 4,
            "asset_in": "A",
            "asset_out": "B",
        },
    }
    if backend == "tau":
        candidate["tau_policy_specs"] = [
            "autotrader_budget_guard_v1",
            "autotrader_execution_guard_v1",
            "autotrader_oracle_freshness_guard_v1",
        ]
    return compile_policy_candidate(candidate).strategy


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


def _observation_packet():
    pools = {"p_ab": _pool("p_ab", "A", "B", 1_000, 2_000, 10)}
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=100)
    assert quote is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools, quote_epoch=5)
    primary = build_quote_receipt_signal_packet(receipt=receipt, pools_by_id=pools, current_epoch=6)
    return build_autotrader_observation_packet(
        primary_signal=primary,
        external_signals=(
            ExternalSignalObservation(
                signal_id="sig.advisory.1",
                source_id="newsfeed.alpha",
                source_kind=SignalSourceKind.ADVISORY_EXTERNAL,
                trust_tier=SignalTrustTier.ADVISORY,
                freshness_ok=True,
                auth_ok=False,
                tags=("macro",),
            ),
            ExternalSignalObservation(
                signal_id="sig.attested.1",
                source_id="oracle.alpha",
                source_kind=SignalSourceKind.ATTESTED_EXTERNAL,
                trust_tier=SignalTrustTier.VERIFIED,
                freshness_ok=True,
                auth_ok=True,
                advisory_only=False,
                tags=("oracle",),
            ),
        ),
        signal_source_registry=ExternalSignalSourceRegistry(
            entries=(
                ExternalSignalSourceRegistryEntry(
                    source_id="newsfeed.alpha",
                    source_kind=SignalSourceKind.ADVISORY_EXTERNAL,
                    allowed_trust_tiers=(SignalTrustTier.ADVISORY,),
                    require_advisory_only=True,
                ),
                ExternalSignalSourceRegistryEntry(
                    source_id="oracle.alpha",
                    source_kind=SignalSourceKind.ATTESTED_EXTERNAL,
                    allowed_trust_tiers=(SignalTrustTier.ATTESTED, SignalTrustTier.VERIFIED),
                    require_auth=True,
                    require_freshness=True,
                ),
            )
        ),
        tau_enabled=True,
    )


def _advisory_primary_observation_packet():
    primary = QuoteReceiptSignalPacket(
        current_epoch=6,
        quote_epoch=5,
        asset_in="A",
        asset_out="B",
        amount_in=100,
        amount_out=150,
        receipt_hash="receipt.hash.1",
        source_kind=SignalSourceKind.ADVISORY_EXTERNAL,
        trust_tier=SignalTrustTier.ADVISORY,
        quote_receipt_present=True,
        quote_receipt_verified=True,
        quote_epoch_present=True,
        source_available=True,
        auth_ok=True,
        binding_ok=True,
    )
    return build_autotrader_observation_packet(primary_signal=primary)


def _route_receipt_and_pools():
    pools = {"p_ab": _pool("p_ab", "A", "B", 1_000, 2_000, 10)}
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=100)
    assert quote is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools, quote_epoch=5)
    return receipt, pools


def _toxic_multihop_route_receipt_and_pools():
    pools = {
        "p_ac": _pool("p_ac", "A", "C", 1_000_000, 1_000_000, 0),
        "p_cb": _pool("p_cb", "C", "B", 10, 10, 0),
    }
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=100)
    assert quote is not None
    assert len(quote.legs) == 1
    assert len(quote.legs[0].hops) == 2
    receipt = make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools, quote_epoch=5)
    return receipt, pools


def _split_route_receipt_and_pools():
    pools = {
        "p1": _pool("p1", "A", "B", 1_000, 1_000, 0),
        "p2": _pool("p2", "A", "B", 1_000, 1_000, 0),
    }
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=600)
    assert quote is not None
    assert len(quote.legs) >= 2
    assert all(len(leg.hops) == 1 for leg in quote.legs)
    receipt = make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools, quote_epoch=5)
    return receipt, pools


def test_autotrader_krr_check_options_cover_live_tau_and_shadow_local() -> None:
    local_strategy = _strategy()
    tau_strategy = _strategy(backend="tau")
    observation_packet = _observation_packet()
    history = {
        "history_source_stats": {
            "oracle.alpha": {"total": 4, "submit": 1, "reject": 3, "skip": 0, "submit_rate": 0.25},
        }
    }

    compile_checks = set(autotrader_krr_check_options(strategy=local_strategy, phase="compile"))
    assert "policy::compile_guard" in compile_checks
    assert "tau::compile_contract" in compile_checks

    shadow_checks = set(autotrader_krr_check_options(strategy=local_strategy, phase="shadow"))
    assert "policy::signal_provenance" in shadow_checks
    assert "policy::budget_guard" in shadow_checks
    assert "policy::oracle_freshness" in shadow_checks
    assert "quote::receipt_binding" in shadow_checks
    assert "action::swap_exact_in" in shadow_checks

    live_tau_checks = set(
        autotrader_krr_check_options(
            strategy=tau_strategy,
            phase="live",
            tau_enabled=True,
            observation_packet=observation_packet,
            history_source_stats=history,
        )
    )
    assert "live::wallet_capability" in live_tau_checks
    assert "live::session_state" in live_tau_checks
    assert "live::signer_match" in live_tau_checks
    assert "live::nonce_guard" in live_tau_checks
    assert "tau::signal_provenance_guard" in live_tau_checks
    assert "tau::budget_guard" in live_tau_checks
    assert "tau::execution_guard" in live_tau_checks
    assert "tau::oracle_freshness_guard" in live_tau_checks
    assert "tau::session_state_guard" in live_tau_checks
    assert "tau::wallet_capability_guard" in live_tau_checks
    assert "tau::nonce_guard" in live_tau_checks
    assert "signal::observation_packet" in live_tau_checks
    assert "signal::trusted_primary" in live_tau_checks
    assert "signal::external_advisory_separation" in live_tau_checks
    assert "signal::external_attestation" in live_tau_checks
    assert "signal::source_registry" in live_tau_checks
    assert "signal::source_quality" in live_tau_checks
    assert "signal::source_history" in live_tau_checks


def test_autotrader_krr_check_options_skip_primary_and_external_advisory_checks_when_not_applicable() -> None:
    checks = set(
        autotrader_krr_check_options(
            strategy=_strategy(),
            phase="live",
            observation_packet=_advisory_primary_observation_packet(),
        )
    )
    assert "signal::observation_packet" in checks
    assert "signal::trusted_primary" not in checks
    assert "signal::external_advisory_separation" not in checks


def test_autotrader_krr_history_loaders_and_source_summary_cover_empty_paths() -> None:
    assert _load_history_check_rows(None) == {}
    assert _load_history_check_rows({"history_check_stats": "bad"}) == {}
    assert _load_history_check_rows({"history_check_stats": {"": {"total": 1}, "ok": "bad"}}) == {}

    assert _load_source_history_rows(None) == {}
    assert _load_source_history_rows({"history_source_stats": "bad"}) == {}
    assert _load_source_history_rows({"history_source_stats": {"": {"total": 1}, "ok": "bad"}}) == {}

    assert _source_quality_summary(observation_packet=None) == []


def test_autotrader_krr_merge_helpers_and_local_tau_branches() -> None:
    assert _merge_list("bad", ["a", "b"]) == ["a", "b"]
    assert _merge_list(["", "a", "a", "b"], ["b", "c"]) == ["a", "b", "c"]

    merged_rules = _merge_named_rules(
        [
            {"name": "existing", "score_bias": 1},
            "bad",
            {"name": "existing", "score_bias": 2},
            {"name": ""},
        ],
        (
            {"name": "existing", "score_bias": 3},
            {"name": "new_rule", "score_bias": 4},
            {"name": ""},
        ),
    )
    assert [row["name"] for row in merged_rules] == ["existing", "new_rule"]
    assert _merge_named_rules("bad", ({"name": "only_default"},)) == [{"name": "only_default"}]

    kb = _merge_autotrader_krr_defaults(
        {
            "operator_priors": {
                "autotrader_dca_live_v1": {
                    "check_preferences": ["custom::one"],
                    "score_bias": 0.5,
                }
            },
            "check_priors": {
                "policy::budget_guard": {"score_bias": 0.9},
            },
            "check_family_priors": {
                "policy": {"score_bias": 0.7},
            },
            "semantic_rules": [{"name": "existing_rule", "score_bias": 1.0}],
        }
    )
    live_prior = kb["operator_priors"]["autotrader_dca_live_v1"]
    assert "custom::one" in live_prior["check_preferences"]
    assert "live::nonce_guard" in live_prior["check_preferences"]
    assert live_prior["score_bias"] == 0.5
    assert kb["check_priors"]["policy::budget_guard"]["score_bias"] == 0.9
    assert "tau::compile_contract" in kb["check_priors"]
    assert kb["check_family_priors"]["policy"]["score_bias"] == 0.7
    assert any(rule["name"] == "existing_rule" for rule in kb["semantic_rules"])
    assert any(rule["name"] == "autotrader_tau_bundle" for rule in kb["semantic_rules"])

    exact_out_strategy = strategy_ir_from_dict(
        {
            "strategy_id": "strategy.exact_out",
            "owner_pubkey": "owner.pubkey.1",
            "policy_backend": "local",
            "template": "limit_ladder",
            "asset_universe": ["A", "B"],
            "allowed_actions": ["place_swap_exact_out", "place_order_intent"],
            "notional_caps": {"per_order_max": 10, "per_window_max": 20, "lifetime_max": 40},
            "risk_limits": {
                "max_slippage_bps": 25,
                "max_oracle_staleness_epochs": 5,
                "require_quote_receipts": False,
            },
            "strategy_window": {
                "valid_from_epoch": 1,
                "valid_until_epoch": 10,
                "min_order_spacing_epochs": 1,
            },
            "controls": {"kill_switch_enabled": False, "max_live_orders": 3},
            "template_params": {"asset_in": "A", "asset_out": "B", "ladder_levels": 2},
        }
    )
    shadow_checks = set(autotrader_krr_check_options(strategy=exact_out_strategy, phase="shadow"))
    assert "policy::kill_switch" not in shadow_checks
    assert "quote::receipt_binding" not in shadow_checks
    assert "action::swap_exact_out" in shadow_checks
    assert "action::order_intent" in shadow_checks
    shadow_tau_checks = set(
        autotrader_krr_check_options(
            strategy=exact_out_strategy,
            phase="shadow",
            tau_enabled=True,
        )
    )
    assert "tau::budget_guard" in shadow_tau_checks
    assert "tau::nonce_guard" not in shadow_tau_checks
    local_tau_checks = set(
        autotrader_krr_check_options(
            strategy=exact_out_strategy,
            phase="live",
            tau_enabled=True,
        )
    )
    assert "tau::budget_guard" in local_tau_checks
    assert "tau::nonce_guard" in local_tau_checks

    quality_only_checks = set(
        autotrader_krr_check_options(
            strategy=_strategy(),
            phase="shadow",
            observation_packet=_observation_packet(),
            history_source_stats={"history_source_stats": "bad"},
        )
    )
    assert "signal::source_quality" in quality_only_checks
    assert "signal::source_history" not in quality_only_checks


def test_autotrader_krr_semantic_signature_encodes_pressure_and_phase() -> None:
    strategy = _strategy(backend="tau")
    observation_packet = _observation_packet()
    receipt, pools = _route_receipt_and_pools()
    history = {
        "history_source_stats": {
            "oracle.alpha": {"total": 4, "submit": 1, "reject": 3, "skip": 0, "submit_rate": 0.25},
        }
    }
    route_risk_advice = advise_autotrader_krr(
        strategy=strategy,
        phase="live",
        current_epoch=5,
        backend="python",
        tau_enabled=True,
        observation_packet=observation_packet,
        quote_receipt=receipt,
        pools_by_id=pools,
        history_check_stats=history,
    )
    assert route_risk_advice is not None
    signature = autotrader_krr_semantic_signature(
        strategy=strategy,
        phase="live",
        current_epoch=5,
        source_form="sentence",
        spent_in_window=450,
        lifetime_spent=900,
        live_orders=1,
        nonce_start=8,
        tau_enabled=True,
        observation_packet=observation_packet,
        route_risk_summary=route_risk_advice["route_risk_summary"],
        history_source_stats=history,
    )

    assert "phase=live" in signature
    assert "backend=tau" in signature
    assert "budget_pressure=1" in signature
    assert "live_order_pressure=1" in signature
    assert "tau_enabled=1" in signature
    assert "observation_packet=1" in signature
    assert "primary_trust_tier=verified" in signature
    assert "external_advisory_count=1" in signature
    assert "external_trusted_count=1" in signature
    assert "source_registry_present=1" in signature
    assert "source_history_present=1" in signature
    assert "low_reliability_external_present=1" in signature
    assert "unseen_external_present=1" in signature
    assert "route_risk_present=1" in signature
    assert "route_shape_supported=1" in signature
    assert "source_form=sentence" in signature
    assert "nonce_start=8" in signature

    no_optional_signature = autotrader_krr_semantic_signature(
        strategy=_strategy(),
        phase="compile",
        current_epoch=1,
        source_form=None,
        nonce_start=None,
    )
    assert "source_form=" not in no_optional_signature
    assert "nonce_start=" not in no_optional_signature


def test_advise_autotrader_krr_is_fail_closed_for_off_and_specialized_for_live() -> None:
    strategy = _strategy(backend="tau")
    history = {
        "schema": "zenodex/autotrader-krr-history/v1",
        "history_check_stats": {
            "policy::budget_guard": {"total": 3, "supported": 2, "support_rate": 2 / 3},
        },
        "history_source_stats": {
            "oracle.alpha": {
                "total": 4,
                "submit": 1,
                "reject": 3,
                "skip": 0,
                "trusted": 4,
                "advisory": 0,
                "registered": 4,
                "auth_ok": 4,
                "freshness_ok": 4,
                "submit_rate": 0.25,
            }
        },
    }

    assert (
        advise_autotrader_krr(
            strategy=strategy,
            phase="live",
            current_epoch=5,
            backend="off",
        )
        is None
    )

    receipt, pools = _route_receipt_and_pools()
    advice = advise_autotrader_krr(
        strategy=strategy,
        phase="live",
        current_epoch=5,
        backend="python",
        spent_in_window=450,
        lifetime_spent=900,
        live_orders=1,
        nonce_start=8,
        tau_enabled=True,
        observation_packet=_observation_packet(),
        quote_receipt=receipt,
        pools_by_id=pools,
        history_check_stats=history,
    )

    assert advice is not None
    assert advice["schema"] == "autotrader/strategy_ir/v1"
    assert advice["phase"] == "live"
    assert advice["operator_id"] == "autotrader_dca_live_v1"
    assert advice["tau_enabled"] is True
    assert "phase=live" in advice["semantic_signature"]
    assert "route_risk_present=1" in advice["semantic_signature"]
    assert "live::signer_match" in advice["candidate_checks"]
    assert advice["backend_used"] == "python"
    assert advice["observation_summary"]["primary_trust_tier"] == "verified"
    assert advice["observation_summary"]["external_signal_count"] == 2
    assert advice["observation_summary"]["trusted_external_signal_count"] == 1
    assert advice["observation_summary"]["advisory_external_signal_count"] == 1
    assert advice["observation_summary"]["source_registry_present"] is True
    assert advice["observation_summary"]["source_history_present"] is True
    assert advice["observation_summary"]["low_reliability_external_count"] == 1
    assert advice["observation_summary"]["unseen_external_count"] == 1
    assert advice["source_history_present"] is True
    assert advice["route_risk_summary"] is not None
    assert advice["route_risk_summary"]["route_shape_supported_for_intents"] is True
    assert advice["route_risk_summary"]["multi_hop_present"] is False
    assert len(advice["source_quality_summary"]) == 2
    oracle_row = next(row for row in advice["source_quality_summary"] if row["source_id"] == "oracle.alpha")
    news_row = next(row for row in advice["source_quality_summary"] if row["source_id"] == "newsfeed.alpha")
    assert oracle_row["registered"] is True
    assert oracle_row["history_total"] == 4
    assert oracle_row["low_reliability"] is True
    assert news_row["registered"] is True
    assert news_row["history_total"] == 0
    assert news_row["unseen_history"] is True
    preferred = set(advice["preferred_checks"])
    assert "live::signer_match" in preferred
    assert "live::nonce_guard" in preferred
    assert "tau::budget_guard" in preferred
    assert "tau::execution_guard" in preferred
    assert "signal::source_history" in advice["candidate_checks"]
    assert "quote::route_shape_support" in advice["candidate_checks"]
    assert "quote::route_economic_sanity" in advice["candidate_checks"]


def test_advise_autotrader_krr_flags_toxic_multihop_route_risk() -> None:
    receipt, pools = _toxic_multihop_route_receipt_and_pools()
    advice = advise_autotrader_krr(
        strategy=_strategy(),
        phase="shadow",
        current_epoch=5,
        backend="python",
        quote_receipt=receipt,
        pools_by_id=pools,
    )

    assert advice is not None
    assert advice["route_risk_summary"] is not None
    route = advice["route_risk_summary"]
    assert route["receipt_verified"] is True
    assert route["multi_hop_present"] is True
    assert route["route_shape_supported_for_intents"] is False
    assert route["max_hop_input_vs_reserve_bps"] >= 10_000
    assert route["extreme_input_stress_present"] is True
    assert route["extreme_output_depletion_present"] is True
    assert advice["confidence_cap"] == 0.15
    assert advice["confidence"] <= advice["ranking_confidence"]
    assert "route_shape_unsupported" in advice["advisory_risk_flags"]
    assert "route_multi_hop_present" in advice["advisory_risk_flags"]
    assert "route_extreme_input_stress" in advice["advisory_risk_flags"]
    assert "quote::route_shape_support" in advice["candidate_checks"]
    assert "quote::route_economic_sanity" in advice["candidate_checks"]


def test_advise_autotrader_krr_accepts_supported_split_single_hop_route_shape() -> None:
    receipt, pools = _split_route_receipt_and_pools()
    advice = advise_autotrader_krr(
        strategy=_strategy(),
        phase="shadow",
        current_epoch=5,
        backend="python",
        quote_receipt=receipt,
        pools_by_id=pools,
    )

    assert advice is not None
    route = advice["route_risk_summary"]
    assert route is not None
    assert route["receipt_verified"] is True
    assert route["leg_count"] >= 2
    assert route["multi_hop_present"] is False
    assert route["route_shape_supported_for_intents"] is True
    assert "route_shape_unsupported" not in advice["advisory_risk_flags"]
