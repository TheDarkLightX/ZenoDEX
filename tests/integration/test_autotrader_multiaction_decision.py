from __future__ import annotations

from dataclasses import replace

import pytest

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
from src.integration.autotrader_multiaction_decision import (
    BoundedMultiActionCandidateSet,
    BoundedMultiActionDecisionCertificate,
    MultiActionCandidateKind,
    MultiActionDecisionCandidate,
    build_bounded_multi_action_candidate_set,
    build_bounded_multi_action_decision_certificate,
    check_bounded_multi_action_decision_tau_argmax_contract,
    derive_bounded_multi_action_decision_binding_ok,
    derive_multi_action_candidate_key,
    verify_bounded_multi_action_candidate_set_payload,
    verify_bounded_multi_action_decision_certificate,
    verify_bounded_multi_action_decision_certificate_payload,
)
from src.kernels.python.strategy_multi_action_candidate_set_contract_v1_adapter import (
    check_strategy_multi_action_candidate_set_contract,
)
from src.integration.autotrader_signals import (
    AutoTraderObservationPacket,
    AutoTraderWalletCapability,
    QuoteReceiptSignalPacket,
)
from src.integration.tau_runner import find_tau_bin
from src.state.canonical import canonical_json_bytes, sha256_hex


def _strategy() -> StrategyIR:
    return StrategyIR(
        strategy_id="multi_action.1",
        owner_pubkey="owner.pubkey.1",
        policy_backend=PolicyBackend.LOCAL,
        template=StrategyTemplate.DCA,
        asset_universe=("BTC", "zUSD"),
        allowed_actions=(
            StrategyAction.PLACE_SWAP_EXACT_IN,
            StrategyAction.PLACE_SWAP_EXACT_OUT,
            StrategyAction.PLACE_ORDER_INTENT,
        ),
        notional_caps=NotionalCaps(per_order_max=100, per_window_max=500, lifetime_max=1_000),
        risk_limits=RiskLimits(max_slippage_bps=50, max_oracle_staleness_epochs=3),
        strategy_window=StrategyWindow(valid_from_epoch=1, valid_until_epoch=100),
        template_params={"fixed_order_size": 100, "cadence_epochs": 4, "asset_in": "zUSD", "asset_out": "BTC"},
    )


def _packet() -> AutoTraderObservationPacket:
    return AutoTraderObservationPacket(
        current_epoch=10,
        primary_signal=QuoteReceiptSignalPacket(
            current_epoch=10,
            quote_epoch=9,
            asset_in="zUSD",
            asset_out="BTC",
            amount_in=100,
            amount_out=95,
            receipt_hash="receipt.hash.multi.1",
        ),
        wallet_capability=AutoTraderWalletCapability(
            session_id="session.1",
            owner_pubkey="owner.pubkey.1",
            chain_id="tau-net-alpha",
            valid_from_epoch=1,
            valid_until_epoch=100,
            notional_remaining=500,
            allowed_assets=("BTC", "zUSD"),
            allowed_actions=(
                StrategyAction.PLACE_SWAP_EXACT_IN,
                StrategyAction.PLACE_SWAP_EXACT_OUT,
                StrategyAction.PLACE_ORDER_INTENT,
            ),
        ),
        tau_enabled=False,
    )


def _artifact_bundle() -> tuple[object, object]:
    strategy = _strategy()
    bundle = build_tau_policy_bundle(
        strategy=strategy,
        compile_contract_tau_receipt=build_compile_contract_tau_policy_receipt(strategy=strategy).to_dict(),
    )
    artifact = build_strategy_policy_artifact(strategy=strategy, tau_policy_bundle=bundle)
    return artifact, bundle


def test_bounded_multi_action_candidate_set_and_decision_choose_highest_priority_requested_action() -> None:
    artifact, bundle = _artifact_bundle()
    candidate_set = build_bounded_multi_action_candidate_set(
        policy_artifact=artifact,
        tau_policy_bundle=bundle,
        observation_packet=_packet(),
        action_frontier={
            StrategyAction.PLACE_SWAP_EXACT_IN: (True, True, 10),
            StrategyAction.PLACE_SWAP_EXACT_OUT: (True, True, 30),
            StrategyAction.PLACE_ORDER_INTENT: (True, True, 20),
        },
    )
    decision = build_bounded_multi_action_decision_certificate(candidate_set=candidate_set)

    assert candidate_set.candidates[0].kind is MultiActionCandidateKind.NO_OP
    assert decision.winner_kind is MultiActionCandidateKind.PLACE_SWAP_EXACT_OUT
    assert decision.winner_index == 3
    assert decision.frontier_width == 4


def test_bounded_multi_action_decision_falls_back_to_noop_when_actions_not_live() -> None:
    artifact, bundle = _artifact_bundle()
    candidate_set = build_bounded_multi_action_candidate_set(
        policy_artifact=artifact,
        tau_policy_bundle=bundle,
        observation_packet=_packet(),
        action_frontier={
            StrategyAction.PLACE_SWAP_EXACT_IN: (False, True, 50),
            StrategyAction.PLACE_SWAP_EXACT_OUT: (True, False, 60),
            StrategyAction.PLACE_ORDER_INTENT: (False, False, 70),
        },
    )
    decision = build_bounded_multi_action_decision_certificate(candidate_set=candidate_set)

    assert decision.winner_kind is MultiActionCandidateKind.NO_OP
    assert decision.winner_index == 0


def test_bounded_multi_action_decision_tie_break_prefers_lower_index() -> None:
    artifact, bundle = _artifact_bundle()
    candidate_set = build_bounded_multi_action_candidate_set(
        policy_artifact=artifact,
        tau_policy_bundle=bundle,
        observation_packet=_packet(),
        action_frontier={
            StrategyAction.PLACE_ORDER_INTENT: (True, True, 20),
            StrategyAction.PLACE_SWAP_EXACT_IN: (True, True, 20),
            StrategyAction.PLACE_SWAP_EXACT_OUT: (True, True, 20),
        },
    )
    decision = build_bounded_multi_action_decision_certificate(candidate_set=candidate_set)

    assert decision.winner_kind is MultiActionCandidateKind.PLACE_ORDER_INTENT
    assert decision.winner_index == 1


def test_bounded_multi_action_decision_roundtrip_and_tamper_rejection() -> None:
    artifact, bundle = _artifact_bundle()
    candidate_set = build_bounded_multi_action_candidate_set(
        policy_artifact=artifact,
        tau_policy_bundle=bundle,
        observation_packet=_packet(),
        action_frontier={
            StrategyAction.PLACE_SWAP_EXACT_IN: (True, True, 10),
            StrategyAction.PLACE_SWAP_EXACT_OUT: (True, True, 30),
            StrategyAction.PLACE_ORDER_INTENT: (True, False, 40),
        },
    )
    decision = build_bounded_multi_action_decision_certificate(candidate_set=candidate_set)

    assert derive_bounded_multi_action_decision_binding_ok(
        candidate_set=candidate_set,
        winner_index=decision.winner_index,
        winner_key=decision.winner_key,
    ) is True
    ok, err = verify_bounded_multi_action_decision_certificate(
        candidate_set=candidate_set,
        certificate=decision,
    )
    assert ok is True
    assert err is None
    assert candidate_set.candidate_set_hash_hex() == sha256_hex(
        canonical_json_bytes(candidate_set.to_unsigned_dict())
    )
    assert decision.decision_hash_hex() == sha256_hex(canonical_json_bytes(decision.to_unsigned_dict()))

    ok, err = verify_bounded_multi_action_candidate_set_payload(candidate_set.to_dict())
    assert ok is True
    assert err is None
    contract = check_strategy_multi_action_candidate_set_contract(candidate_set)
    assert contract.ok is True
    assert contract.error is None
    ok, err = verify_bounded_multi_action_decision_certificate_payload(decision.to_dict())
    assert ok is True
    assert err is None

    bad_decision_payload = decision.to_dict()
    bad_decision_payload["winner_key"] = 7
    ok, err = verify_bounded_multi_action_decision_certificate_payload(bad_decision_payload)
    assert ok is False
    assert err == "decision_hash mismatch"

    bad_candidate_payload = candidate_set.to_dict()
    bad_candidate_payload["candidates"][1]["candidate_key"] = 7
    ok, err = verify_bounded_multi_action_candidate_set_payload(bad_candidate_payload)
    assert ok is False
    assert err == "candidate_set_hash mismatch"


def test_bounded_multi_action_payload_verifiers_reject_hash_valid_malformed_shapes() -> None:
    artifact, bundle = _artifact_bundle()
    candidate_set = build_bounded_multi_action_candidate_set(
        policy_artifact=artifact,
        tau_policy_bundle=bundle,
        observation_packet=_packet(),
        action_frontier={
            StrategyAction.PLACE_SWAP_EXACT_IN: (True, True, 10),
            StrategyAction.PLACE_SWAP_EXACT_OUT: (True, True, 30),
            StrategyAction.PLACE_ORDER_INTENT: (True, False, 40),
        },
    )
    decision = build_bounded_multi_action_decision_certificate(candidate_set=candidate_set)

    candidate_payload = candidate_set.to_dict()
    candidate_payload["candidates"] = ["bad"]
    candidate_unsigned = {
        key: value
        for key, value in candidate_payload.items()
        if key != "candidate_set_hash"
    }
    candidate_payload["candidate_set_hash"] = sha256_hex(
        canonical_json_bytes(candidate_unsigned)
    )
    ok, err = verify_bounded_multi_action_candidate_set_payload(candidate_payload)
    assert ok is False
    assert err == "candidate must be an object"

    candidate_payload = candidate_set.to_dict()
    del candidate_payload["candidates"][1]["action_priority"]
    candidate_unsigned = {
        key: value
        for key, value in candidate_payload.items()
        if key != "candidate_set_hash"
    }
    candidate_payload["candidate_set_hash"] = sha256_hex(
        canonical_json_bytes(candidate_unsigned)
    )
    ok, err = verify_bounded_multi_action_candidate_set_payload(candidate_payload)
    assert ok is False
    assert err == "candidate missing field: action_priority"

    decision_payload = decision.to_dict()
    decision_payload["argmax_steps"] = ["bad"]
    decision_unsigned = {
        key: value
        for key, value in decision_payload.items()
        if key != "decision_hash"
    }
    decision_payload["decision_hash"] = sha256_hex(
        canonical_json_bytes(decision_unsigned)
    )
    ok, err = verify_bounded_multi_action_decision_certificate_payload(decision_payload)
    assert ok is False
    assert err == "argmax step must be an object"

    decision_payload = decision.to_dict()
    decision_payload["frontier_width"] = True
    decision_unsigned = {
        key: value
        for key, value in decision_payload.items()
        if key != "decision_hash"
    }
    decision_payload["decision_hash"] = sha256_hex(
        canonical_json_bytes(decision_unsigned)
    )
    ok, err = verify_bounded_multi_action_decision_certificate_payload(decision_payload)
    assert ok is False
    assert err == "frontier_width must be an int"


def test_bounded_multi_action_candidate_set_contract_rejects_mutated_shape() -> None:
    artifact, bundle = _artifact_bundle()
    candidate_set = build_bounded_multi_action_candidate_set(
        policy_artifact=artifact,
        tau_policy_bundle=bundle,
        observation_packet=_packet(),
        action_frontier={
            StrategyAction.PLACE_SWAP_EXACT_IN: (True, True, 10),
            StrategyAction.PLACE_SWAP_EXACT_OUT: (True, True, 30),
        },
    )
    mutated_candidate = replace(candidate_set.candidates[1], candidate_index=7)
    object.__setattr__(
        candidate_set,
        "candidates",
        (candidate_set.candidates[0], mutated_candidate, candidate_set.candidates[2]),
    )

    contract = check_strategy_multi_action_candidate_set_contract(candidate_set)
    assert contract.ok is False
    assert contract.error == "candidate_indices_noncontiguous"


def test_bounded_multi_action_models_reject_invalid_shapes() -> None:
    with pytest.raises(TypeError, match="requested must be a bool"):
        derive_multi_action_candidate_key(
            requested="yes",  # type: ignore[arg-type]
            admissible=True,
            action_priority=1,
        )
    with pytest.raises(ValueError, match="action_priority out of range"):
        derive_multi_action_candidate_key(
            requested=True,
            admissible=True,
            action_priority=-1,
        )
    with pytest.raises(ValueError, match="NO_OP candidate must have action_priority = 0"):
        MultiActionDecisionCandidate(
            candidate_index=0,
            kind=MultiActionCandidateKind.NO_OP,
            requested=True,
            admissible=True,
            action_priority=1,
            candidate_key=derive_multi_action_candidate_key(
                requested=True,
                admissible=True,
                action_priority=1,
            ),
        )
    with pytest.raises(ValueError, match="bounded multi-action candidate set must contain at least two candidates"):
        BoundedMultiActionCandidateSet(
            policy_artifact_hash="a",
            tau_policy_bundle_hash="b",
            observation_hash="c",
            decision_model_version="d",
            candidates=(
                MultiActionDecisionCandidate(
                    candidate_index=0,
                    kind=MultiActionCandidateKind.NO_OP,
                    requested=True,
                    admissible=True,
                    action_priority=0,
                    candidate_key=derive_multi_action_candidate_key(
                        requested=True,
                        admissible=True,
                        action_priority=0,
                    ),
                ),
            ),
        )


def test_bounded_multi_action_tau_argmax_contract_replays_when_tau_enabled() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    artifact, bundle = _artifact_bundle()
    candidate_set = build_bounded_multi_action_candidate_set(
        policy_artifact=artifact,
        tau_policy_bundle=bundle,
        observation_packet=_packet(),
        action_frontier={
            StrategyAction.PLACE_SWAP_EXACT_IN: (True, True, 10),
            StrategyAction.PLACE_SWAP_EXACT_OUT: (True, True, 30),
            StrategyAction.PLACE_ORDER_INTENT: (True, False, 40),
        },
    )
    decision = build_bounded_multi_action_decision_certificate(candidate_set=candidate_set)

    result = check_bounded_multi_action_decision_tau_argmax_contract(
        candidate_set=candidate_set,
        certificate=decision,
        tau_bin=tau_bin,
        timeout_s=10.0,
    )

    assert result.ok is True
    assert result.tau_enabled is True
    assert result.tau_used is True
    assert result.certificate_ok is True
    assert result.binding_ok is True
    assert result.frontier_width_ok is True
    assert result.argmax_steps_ok is True
    assert result.step_count == 4
    assert result.error is None
    with pytest.raises(ValueError, match="candidate indices must be contiguous from 0"):
        BoundedMultiActionCandidateSet(
            policy_artifact_hash="a",
            tau_policy_bundle_hash="b",
            observation_hash="c",
            decision_model_version="d",
            candidates=(
                MultiActionDecisionCandidate(
                    candidate_index=0,
                    kind=MultiActionCandidateKind.NO_OP,
                    requested=True,
                    admissible=True,
                    action_priority=0,
                    candidate_key=derive_multi_action_candidate_key(
                        requested=True,
                        admissible=True,
                        action_priority=0,
                    ),
                ),
                MultiActionDecisionCandidate(
                    candidate_index=2,
                    kind=MultiActionCandidateKind.PLACE_SWAP_EXACT_IN,
                    requested=True,
                    admissible=True,
                    action_priority=1,
                    candidate_key=derive_multi_action_candidate_key(
                        requested=True,
                        admissible=True,
                        action_priority=1,
                    ),
                ),
            ),
        )
    with pytest.raises(TypeError, match="action_frontier must be a mapping"):
        build_bounded_multi_action_candidate_set(  # type: ignore[arg-type]
            policy_artifact=_artifact_bundle()[0],
            tau_policy_bundle=_artifact_bundle()[1],
            observation_packet=_packet(),
            action_frontier=[],
        )
    with pytest.raises(TypeError, match="action_frontier keys must be StrategyAction members"):
        build_bounded_multi_action_candidate_set(  # type: ignore[arg-type]
            policy_artifact=_artifact_bundle()[0],
            tau_policy_bundle=_artifact_bundle()[1],
            observation_packet=_packet(),
            action_frontier={"bad": (True, True, 1)},
        )
    with pytest.raises(TypeError, match="action_frontier values must be \\(requested, admissible, action_priority\\) tuples"):
        build_bounded_multi_action_candidate_set(  # type: ignore[arg-type]
            policy_artifact=_artifact_bundle()[0],
            tau_policy_bundle=_artifact_bundle()[1],
            observation_packet=_packet(),
            action_frontier={StrategyAction.PLACE_SWAP_EXACT_IN: {"requested": True}},
        )
    with pytest.raises(TypeError, match="candidate_set must be a BoundedMultiActionCandidateSet"):
        build_bounded_multi_action_decision_certificate(candidate_set="bad")  # type: ignore[arg-type]


def test_bounded_multi_action_decision_verifier_rejects_mismatch() -> None:
    artifact, bundle = _artifact_bundle()
    candidate_set = build_bounded_multi_action_candidate_set(
        policy_artifact=artifact,
        tau_policy_bundle=bundle,
        observation_packet=_packet(),
        action_frontier={
            StrategyAction.PLACE_SWAP_EXACT_IN: (True, True, 10),
            StrategyAction.PLACE_SWAP_EXACT_OUT: (True, True, 30),
            StrategyAction.PLACE_ORDER_INTENT: (True, True, 20),
        },
    )
    decision = build_bounded_multi_action_decision_certificate(candidate_set=candidate_set)
    bad = replace(decision, candidate_set_hash="wrong.hash")

    ok, err = verify_bounded_multi_action_decision_certificate(
        candidate_set=candidate_set,
        certificate=bad,
    )
    assert ok is False
    assert err == "candidate_set_hash mismatch"
