from __future__ import annotations

from dataclasses import replace
from types import SimpleNamespace

import pytest

import src.integration.autotrader_decision as autotrader_decision
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
    DecisionCandidateKind,
    StrategyCandidateSet,
    StrategyDecisionCertificate,
    build_strategy_candidate_set,
    build_strategy_decision_certificate,
    derive_strategy_decision_binding_ok,
    verify_strategy_candidate_set_payload,
    verify_strategy_decision_certificate,
    verify_strategy_decision_certificate_payload,
)
from src.integration.autotrader_signals import (
    AutoTraderObservationPacket,
    AutoTraderWalletCapability,
    QuoteReceiptSignalPacket,
)
from src.state.canonical import canonical_json_bytes, sha256_hex


def _strategy() -> StrategyIR:
    return StrategyIR(
        strategy_id="decision.1",
        owner_pubkey="owner.pubkey.1",
        policy_backend=PolicyBackend.LOCAL,
        template=StrategyTemplate.DCA,
        asset_universe=("BTC", "zUSD"),
        allowed_actions=(StrategyAction.PLACE_SWAP_EXACT_IN,),
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
            receipt_hash="receipt.hash.1",
        ),
        wallet_capability=AutoTraderWalletCapability(
            session_id="session.1",
            owner_pubkey="owner.pubkey.1",
            chain_id="tau-net-alpha",
            valid_from_epoch=1,
            valid_until_epoch=100,
            notional_remaining=500,
            allowed_assets=("BTC", "zUSD"),
            allowed_actions=(StrategyAction.PLACE_SWAP_EXACT_IN,),
        ),
        tau_enabled=False,
    )


def test_candidate_set_and_decision_emit_vs_noop() -> None:
    strategy = _strategy()
    bundle = build_tau_policy_bundle(
        strategy=strategy,
        compile_contract_tau_receipt=build_compile_contract_tau_policy_receipt(strategy=strategy).to_dict(),
    )
    artifact = build_strategy_policy_artifact(strategy=strategy, tau_policy_bundle=bundle)
    candidate_set = build_strategy_candidate_set(
        policy_artifact=artifact,
        tau_policy_bundle=bundle,
        observation_packet=_packet(),
        emit_requested=True,
        emit_admissible=True,
    )
    decision = build_strategy_decision_certificate(candidate_set=candidate_set, kill_switch_active=False)
    assert candidate_set.candidates[0].kind is DecisionCandidateKind.NO_OP
    assert candidate_set.candidates[1].kind is DecisionCandidateKind.EMIT_COMPILED_INTENT
    assert decision.winner_index == 1
    assert decision.winner_kind is DecisionCandidateKind.EMIT_COMPILED_INTENT


def test_candidate_set_and_decision_noop_on_kill_switch() -> None:
    strategy = _strategy()
    bundle = build_tau_policy_bundle(
        strategy=strategy,
        compile_contract_tau_receipt=build_compile_contract_tau_policy_receipt(strategy=strategy).to_dict(),
    )
    artifact = build_strategy_policy_artifact(strategy=strategy, tau_policy_bundle=bundle)
    candidate_set = build_strategy_candidate_set(
        policy_artifact=artifact,
        tau_policy_bundle=bundle,
        observation_packet=_packet(),
        emit_requested=True,
        emit_admissible=True,
    )
    decision = build_strategy_decision_certificate(candidate_set=candidate_set, kill_switch_active=True)
    assert decision.winner_index == 0
    assert decision.winner_kind is DecisionCandidateKind.NO_OP


def test_decision_certificate_binding_and_verification_round_trip() -> None:
    strategy = _strategy()
    bundle = build_tau_policy_bundle(
        strategy=strategy,
        compile_contract_tau_receipt=build_compile_contract_tau_policy_receipt(strategy=strategy).to_dict(),
    )
    artifact = build_strategy_policy_artifact(strategy=strategy, tau_policy_bundle=bundle)
    candidate_set = build_strategy_candidate_set(
        policy_artifact=artifact,
        tau_policy_bundle=bundle,
        observation_packet=_packet(),
        emit_requested=True,
        emit_admissible=True,
    )
    decision = build_strategy_decision_certificate(candidate_set=candidate_set, kill_switch_active=False)

    assert derive_strategy_decision_binding_ok(
        candidate_set=candidate_set,
        winner_index=decision.winner_index,
        winner_key=decision.winner_key,
        kill_switch_active=False,
    ) is True
    ok, err = verify_strategy_decision_certificate(
        candidate_set=candidate_set,
        certificate=decision,
        expected_kill_switch_active=False,
    )
    assert ok is True
    assert err is None
    assert candidate_set.candidate_set_hash_hex() == sha256_hex(canonical_json_bytes(candidate_set.to_unsigned_dict()))
    assert decision.decision_hash_hex() == sha256_hex(canonical_json_bytes(decision.to_unsigned_dict()))
    candidate_payload_ok, candidate_payload_err = verify_strategy_candidate_set_payload(candidate_set.to_dict())
    assert candidate_payload_ok is True
    assert candidate_payload_err is None
    decision_payload_ok, decision_payload_err = verify_strategy_decision_certificate_payload(decision.to_dict())
    assert decision_payload_ok is True
    assert decision_payload_err is None


def test_verify_strategy_decision_certificate_rejects_tampered_binding() -> None:
    strategy = _strategy()
    bundle = build_tau_policy_bundle(
        strategy=strategy,
        compile_contract_tau_receipt=build_compile_contract_tau_policy_receipt(strategy=strategy).to_dict(),
    )
    artifact = build_strategy_policy_artifact(strategy=strategy, tau_policy_bundle=bundle)
    candidate_set = build_strategy_candidate_set(
        policy_artifact=artifact,
        tau_policy_bundle=bundle,
        observation_packet=_packet(),
        emit_requested=True,
        emit_admissible=True,
    )
    decision = build_strategy_decision_certificate(candidate_set=candidate_set, kill_switch_active=False)
    bad = replace(decision, candidate_set_hash="wrong.hash")

    ok, err = verify_strategy_decision_certificate(
        candidate_set=candidate_set,
        certificate=bad,
        expected_kill_switch_active=False,
    )
    assert ok is False
    assert err == "candidate_set_hash mismatch"

    decision_payload = decision.to_dict()
    decision_payload["winner_key"] = 7
    ok, err = verify_strategy_decision_certificate_payload(decision_payload)
    assert ok is False
    assert err == "decision_hash mismatch"

    candidate_payload = candidate_set.to_dict()
    candidate_payload["candidates"][1]["candidate_key"] = 7
    ok, err = verify_strategy_candidate_set_payload(candidate_payload)
    assert ok is False
    assert err == "candidate_set_hash mismatch"


def test_decision_payload_verifiers_reject_hash_valid_malformed_shapes() -> None:
    strategy = _strategy()
    bundle = build_tau_policy_bundle(
        strategy=strategy,
        compile_contract_tau_receipt=build_compile_contract_tau_policy_receipt(strategy=strategy).to_dict(),
    )
    artifact = build_strategy_policy_artifact(strategy=strategy, tau_policy_bundle=bundle)
    candidate_set = build_strategy_candidate_set(
        policy_artifact=artifact,
        tau_policy_bundle=bundle,
        observation_packet=_packet(),
        emit_requested=True,
        emit_admissible=True,
    )
    decision = build_strategy_decision_certificate(
        candidate_set=candidate_set,
        kill_switch_active=False,
    )

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
    ok, err = verify_strategy_candidate_set_payload(candidate_payload)
    assert ok is False
    assert err == "candidate must be an object"

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
    ok, err = verify_strategy_decision_certificate_payload(decision_payload)
    assert ok is False
    assert err == "argmax step must be an object"


def test_decision_models_cover_validation_and_hash_paths(monkeypatch: pytest.MonkeyPatch) -> None:
    strategy = _strategy()
    bundle = build_tau_policy_bundle(
        strategy=strategy,
        compile_contract_tau_receipt=build_compile_contract_tau_policy_receipt(strategy=strategy).to_dict(),
    )
    artifact = build_strategy_policy_artifact(strategy=strategy, tau_policy_bundle=bundle)
    packet = _packet()

    with pytest.raises(TypeError, match="candidate_index must be an int"):
        autotrader_decision.DecisionCandidate(
            candidate_index=True,
            kind=DecisionCandidateKind.NO_OP,
            requested=True,
            admissible=True,
            candidate_key=0,
        )
    with pytest.raises(ValueError, match="candidate_index out of range"):
        autotrader_decision.DecisionCandidate(
            candidate_index=-1,
            kind=DecisionCandidateKind.NO_OP,
            requested=True,
            admissible=True,
            candidate_key=0,
        )
    with pytest.raises(TypeError, match="kind must be a DecisionCandidateKind"):
        autotrader_decision.DecisionCandidate(0, "bad", True, True, 0)  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="requested must be a bool"):
        autotrader_decision.DecisionCandidate(0, DecisionCandidateKind.NO_OP, 1, True, 0)  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="admissible must be a bool"):
        autotrader_decision.DecisionCandidate(0, DecisionCandidateKind.NO_OP, True, 1, 0)  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="candidate_key must be an int"):
        autotrader_decision.DecisionCandidate(0, DecisionCandidateKind.NO_OP, True, True, False)  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="candidate_key out of range"):
        autotrader_decision.DecisionCandidate(0, DecisionCandidateKind.NO_OP, True, True, -1)

    good_candidates = (
        autotrader_decision.DecisionCandidate(0, DecisionCandidateKind.NO_OP, True, True, 0),
        autotrader_decision.DecisionCandidate(1, DecisionCandidateKind.EMIT_COMPILED_INTENT, True, True, 1),
    )
    with pytest.raises(ValueError, match="policy_artifact_hash must be a non-empty string"):
        StrategyCandidateSet("", "b", "c", "d", good_candidates)
    with pytest.raises(ValueError, match="candidate set must contain exactly two candidates"):
        StrategyCandidateSet("a", "b", "c", "d", good_candidates[:1])
    with pytest.raises(ValueError, match="candidate 0 must be NO_OP"):
        StrategyCandidateSet(
            "a",
            "b",
            "c",
            "d",
            (
                autotrader_decision.DecisionCandidate(0, DecisionCandidateKind.EMIT_COMPILED_INTENT, True, True, 0),
                good_candidates[1],
            ),
        )
    with pytest.raises(ValueError, match="candidate 1 must be EMIT_COMPILED_INTENT"):
        StrategyCandidateSet(
            "a",
            "b",
            "c",
            "d",
            (
                good_candidates[0],
                autotrader_decision.DecisionCandidate(1, DecisionCandidateKind.NO_OP, True, True, 0),
            ),
        )

    candidate_set = build_strategy_candidate_set(
        policy_artifact=artifact,
        tau_policy_bundle=bundle,
        observation_packet=packet,
        emit_requested=False,
        emit_admissible=False,
    )
    assert candidate_set.to_dict()["schema"] == autotrader_decision.CANDIDATE_SET_SCHEMA
    decision = build_strategy_decision_certificate(candidate_set=candidate_set, kill_switch_active=False)
    assert decision.to_dict()["schema"] == autotrader_decision.DECISION_CERTIFICATE_SCHEMA
    assert decision.winner_index == 0

    with pytest.raises(TypeError, match="packet must be an AutoTraderObservationPacket"):
        autotrader_decision.observation_hash_hex("bad")  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="policy_artifact must be a StrategyPolicyArtifact"):
        build_strategy_candidate_set(
            policy_artifact="bad",  # type: ignore[arg-type]
            tau_policy_bundle=bundle,
            observation_packet=packet,
            emit_requested=True,
            emit_admissible=True,
        )
    with pytest.raises(TypeError, match="tau_policy_bundle must be a TauPolicyBundle"):
        build_strategy_candidate_set(
            policy_artifact=artifact,
            tau_policy_bundle="bad",  # type: ignore[arg-type]
            observation_packet=packet,
            emit_requested=True,
            emit_admissible=True,
        )
    monkeypatch.setattr(
        autotrader_decision,
        "check_strategy_candidate_set_contract",
        lambda candidate_set: SimpleNamespace(ok=False, error="bad_shape"),
    )
    with pytest.raises(ValueError, match="candidate set contract rejected: bad_shape"):
        build_strategy_candidate_set(
            policy_artifact=artifact,
            tau_policy_bundle=bundle,
            observation_packet=packet,
            emit_requested=True,
            emit_admissible=True,
        )
    with pytest.raises(TypeError, match="candidate_set must be a StrategyCandidateSet"):
        build_strategy_decision_certificate(candidate_set="bad", kill_switch_active=False)  # type: ignore[arg-type]


def test_decision_certificate_validation_edges() -> None:
    with pytest.raises(ValueError, match="policy_artifact_hash must be a non-empty string"):
        StrategyDecisionCertificate("", "b", "c", "d", "e", 0, DecisionCandidateKind.NO_OP, 0, ({"x": 1},), False)
    with pytest.raises(TypeError, match="winner_index must be an int"):
        StrategyDecisionCertificate("a", "b", "c", "d", "e", True, DecisionCandidateKind.NO_OP, 0, ({"x": 1},), False)  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="winner_index must be 0 or 1"):
        StrategyDecisionCertificate("a", "b", "c", "d", "e", 2, DecisionCandidateKind.NO_OP, 0, ({"x": 1},), False)
    with pytest.raises(TypeError, match="winner_kind must be a DecisionCandidateKind"):
        StrategyDecisionCertificate("a", "b", "c", "d", "e", 0, "bad", 0, ({"x": 1},), False)  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="winner_key must be an int"):
        StrategyDecisionCertificate("a", "b", "c", "d", "e", 0, DecisionCandidateKind.NO_OP, False, ({"x": 1},), False)  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="winner_key out of range"):
        StrategyDecisionCertificate("a", "b", "c", "d", "e", 0, DecisionCandidateKind.NO_OP, -1, ({"x": 1},), False)
    with pytest.raises(TypeError, match="kill_switch_active must be a bool"):
        StrategyDecisionCertificate("a", "b", "c", "d", "e", 0, DecisionCandidateKind.NO_OP, 0, ({"x": 1},), 1)  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="argmax_steps must be non-empty"):
        StrategyDecisionCertificate("a", "b", "c", "d", "e", 0, DecisionCandidateKind.NO_OP, 0, (), False)
    with pytest.raises(TypeError, match="emit_requested must be a bool"):
        autotrader_decision.check_strategy_decision_kernel(
            emit_requested="yes",  # type: ignore[arg-type]
            emit_admissible=True,
        )
    with pytest.raises(TypeError, match="kill_switch_active must be a bool"):
        autotrader_decision.check_strategy_kill_switch_guard(
            kill_switch_enabled=True,
            kill_switch_active="yes",  # type: ignore[arg-type]
        )
