from __future__ import annotations

import pytest

from src.agents.policy_artifacts import (
    StrategyPolicyArtifact,
    TauPolicyBundle,
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
    StrategyIR,
    StrategyTemplate,
    StrategyWindow,
)
from src.agents.tau_policy_adapter import (
    build_compilation_witness_tau_policy_receipt,
    build_compile_contract_tau_policy_receipt,
)
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey
from src.kernels.python.strategy_policy_artifact_contract_v1_adapter import (
    check_strategy_policy_artifact_contract,
)
from src.kernels.python.strategy_policy_bundle_contract_v1_adapter import (
    check_strategy_policy_bundle_contract,
)


def _strategy(owner_pubkey: str) -> StrategyIR:
    return StrategyIR(
        strategy_id="contracts.1",
        owner_pubkey=owner_pubkey,
        policy_backend=PolicyBackend.LOCAL,
        template=StrategyTemplate.DCA,
        asset_universe=("BTC", "zUSD"),
        allowed_actions=(StrategyAction.PLACE_SWAP_EXACT_IN,),
        notional_caps=NotionalCaps(per_order_max=100, per_window_max=500, lifetime_max=1_000),
        risk_limits=RiskLimits(max_slippage_bps=50, max_oracle_staleness_epochs=3),
        strategy_window=StrategyWindow(valid_from_epoch=1, valid_until_epoch=100),
        template_params={"fixed_order_size": 100, "cadence_epochs": 4, "asset_in": "zUSD", "asset_out": "BTC"},
    )


def test_policy_bundle_and_artifact_contract_accept_path() -> None:
    privkey = 17
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _strategy(owner_pubkey)
    source_artifact = build_strategy_source_artifact(strategy=strategy, source_form="kv")
    bundle = build_tau_policy_bundle(
        strategy=strategy,
        compile_contract_tau_receipt=build_compile_contract_tau_policy_receipt(strategy=strategy).to_dict(),
        source_artifact=source_artifact,
    )
    artifact = sign_strategy_policy_artifact(
        build_strategy_policy_artifact(
            strategy=strategy,
            tau_policy_bundle=bundle,
            source_artifact=source_artifact,
        ),
        privkey=privkey,
    )

    bundle_result = check_strategy_policy_bundle_contract(bundle)
    assert bundle_result.ok is True
    assert bundle_result.evidence_class_ok is True
    assert check_strategy_policy_artifact_contract(artifact, tau_policy_bundle=bundle).ok is True


def test_policy_bundle_contract_rejects_evidence_class_below_live_floor() -> None:
    privkey = 29
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _strategy(owner_pubkey)
    source_artifact = build_strategy_source_artifact(strategy=strategy, source_form="kv")
    good_bundle = build_tau_policy_bundle(
        strategy=strategy,
        compile_contract_tau_receipt=build_compile_contract_tau_policy_receipt(strategy=strategy).to_dict(),
        source_artifact=source_artifact,
    )
    low_evidence_bundle = TauPolicyBundle(
        strategy_hash=good_bundle.strategy_hash,
        owner_pubkey=good_bundle.owner_pubkey,
        source_artifact_hash=good_bundle.source_artifact_hash,
        required_spec_ids=good_bundle.required_spec_ids,
        compile_contract_tau_receipt=good_bundle.compile_contract_tau_receipt,
        compilation_witness_tau_receipt=good_bundle.compilation_witness_tau_receipt,
        decision_model_version=good_bundle.decision_model_version,
        evidence_class="O2",
    )

    result = check_strategy_policy_bundle_contract(low_evidence_bundle)

    assert result.ok is False
    assert result.strategy_hash_ok is True
    assert result.owner_binding_ok is True
    assert result.source_artifact_hash_ok is True
    assert result.canonical_specs_ok is True
    assert result.compile_contract_ok is True
    assert result.compilation_witness_ok is True
    assert result.decision_model_version_ok is True
    assert result.evidence_class_ok is False
    assert result.error == "evidence_class_below_o3"


def test_policy_artifact_contract_rejects_unsigned_artifact() -> None:
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(19)
    strategy = _strategy(owner_pubkey)
    source_artifact = build_strategy_source_artifact(strategy=strategy, source_form="kv")
    bundle = build_tau_policy_bundle(
        strategy=strategy,
        compile_contract_tau_receipt=build_compile_contract_tau_policy_receipt(strategy=strategy).to_dict(),
        source_artifact=source_artifact,
    )
    artifact = build_strategy_policy_artifact(
        strategy=strategy,
        tau_policy_bundle=bundle,
        source_artifact=source_artifact,
    )
    result = check_strategy_policy_artifact_contract(artifact, tau_policy_bundle=bundle)
    assert result.ok is False
    assert result.error == "signature_missing"


def test_policy_contract_adapters_cover_type_and_error_edges() -> None:
    privkey = 23
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _strategy(owner_pubkey)
    receipt = build_compile_contract_tau_policy_receipt(strategy=strategy).to_dict()
    source_artifact = build_strategy_source_artifact(strategy=strategy, source_form="kv")
    witness_receipt = build_compilation_witness_tau_policy_receipt(
        strategy=strategy,
        source_artifact=source_artifact,
        compile_contract_tau_receipt=receipt,
    ).to_dict()
    bundle = build_tau_policy_bundle(
        strategy=strategy,
        compile_contract_tau_receipt=receipt,
        source_artifact=source_artifact,
    )
    artifact = sign_strategy_policy_artifact(
        build_strategy_policy_artifact(
            strategy=strategy,
            tau_policy_bundle=bundle,
            source_artifact=source_artifact,
        ),
        privkey=privkey,
    )

    with pytest.raises(TypeError, match="bundle must be a TauPolicyBundle"):
        check_strategy_policy_bundle_contract("bad")  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="artifact must be a StrategyPolicyArtifact"):
        check_strategy_policy_artifact_contract("bad", tau_policy_bundle=bundle)  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="tau_policy_bundle must be a TauPolicyBundle"):
        check_strategy_policy_artifact_contract(artifact, tau_policy_bundle="bad")  # type: ignore[arg-type]

    bad_bundle = object.__new__(TauPolicyBundle)
    object.__setattr__(bad_bundle, "strategy_hash", "")
    object.__setattr__(bad_bundle, "owner_pubkey", owner_pubkey)
    object.__setattr__(bad_bundle, "source_artifact_hash", source_artifact.source_artifact_hash_hex())
    object.__setattr__(bad_bundle, "required_spec_ids", AUTOTRADER_TAU_POLICY_SPECS)
    object.__setattr__(bad_bundle, "compile_contract_tau_receipt", receipt)
    object.__setattr__(bad_bundle, "compilation_witness_tau_receipt", witness_receipt)
    object.__setattr__(bad_bundle, "decision_model_version", bundle.decision_model_version)
    object.__setattr__(bad_bundle, "evidence_class", bundle.evidence_class)
    assert check_strategy_policy_bundle_contract(bad_bundle).error == "strategy_hash_missing"

    object.__setattr__(bad_bundle, "strategy_hash", strategy.strategy_hash_hex())
    object.__setattr__(bad_bundle, "owner_pubkey", "")
    assert check_strategy_policy_bundle_contract(bad_bundle).error == "owner_binding_missing"

    object.__setattr__(bad_bundle, "owner_pubkey", owner_pubkey)
    object.__setattr__(bad_bundle, "source_artifact_hash", "")
    assert check_strategy_policy_bundle_contract(bad_bundle).error == "source_artifact_hash_missing"

    object.__setattr__(bad_bundle, "source_artifact_hash", source_artifact.source_artifact_hash_hex())
    object.__setattr__(bad_bundle, "required_spec_ids", ("bad.spec",))
    assert check_strategy_policy_bundle_contract(bad_bundle).error == "canonical_specs_invalid"

    object.__setattr__(bad_bundle, "required_spec_ids", AUTOTRADER_TAU_POLICY_SPECS)
    object.__setattr__(bad_bundle, "compile_contract_tau_receipt", {"expected_ok": False, "spec_id": "autotrader_compile_contract_v1"})
    assert check_strategy_policy_bundle_contract(bad_bundle).error == "compile_contract_tau_receipt_invalid"

    object.__setattr__(bad_bundle, "compile_contract_tau_receipt", receipt)
    object.__setattr__(bad_bundle, "compilation_witness_tau_receipt", {"expected_ok": False, "spec_id": "autotrader_compilation_witness_v1"})
    assert check_strategy_policy_bundle_contract(bad_bundle).error == "compilation_witness_tau_receipt_invalid"

    object.__setattr__(bad_bundle, "compilation_witness_tau_receipt", witness_receipt)
    object.__setattr__(bad_bundle, "decision_model_version", "")
    assert check_strategy_policy_bundle_contract(bad_bundle).error == "decision_model_version_missing"

    object.__setattr__(bad_bundle, "decision_model_version", bundle.decision_model_version)
    object.__setattr__(bad_bundle, "evidence_class", "O2")
    assert check_strategy_policy_bundle_contract(bad_bundle).error == "evidence_class_below_o3"

    wrong_hash_bundle = TauPolicyBundle(
        strategy_hash="0xdead",
        owner_pubkey=owner_pubkey,
        source_artifact_hash=source_artifact.source_artifact_hash_hex(),
        required_spec_ids=AUTOTRADER_TAU_POLICY_SPECS,
        compile_contract_tau_receipt=receipt,
        compilation_witness_tau_receipt=witness_receipt,
    )
    assert check_strategy_policy_artifact_contract(artifact, tau_policy_bundle=wrong_hash_bundle).error == "strategy_hash_mismatch"

    wrong_owner_bundle = TauPolicyBundle(
        strategy_hash=strategy.strategy_hash_hex(),
        owner_pubkey="other.owner",
        source_artifact_hash=source_artifact.source_artifact_hash_hex(),
        required_spec_ids=AUTOTRADER_TAU_POLICY_SPECS,
        compile_contract_tau_receipt=receipt,
        compilation_witness_tau_receipt=witness_receipt,
    )
    assert check_strategy_policy_artifact_contract(artifact, tau_policy_bundle=wrong_owner_bundle).error == "owner_binding_mismatch"

    wrong_source_hash_bundle = TauPolicyBundle(
        strategy_hash=strategy.strategy_hash_hex(),
        owner_pubkey=owner_pubkey,
        source_artifact_hash="0xdead",
        required_spec_ids=AUTOTRADER_TAU_POLICY_SPECS,
        compile_contract_tau_receipt=receipt,
        compilation_witness_tau_receipt=witness_receipt,
    )
    assert check_strategy_policy_artifact_contract(artifact, tau_policy_bundle=wrong_source_hash_bundle).error == "source_artifact_hash_mismatch"

    wrong_hash_artifact = StrategyPolicyArtifact(
        strategy=artifact.strategy,
        source_artifact_hash=artifact.source_artifact_hash,
        tau_policy_bundle_hash="0xdead",
        decision_model_version=artifact.decision_model_version,
        signature=artifact.signature,
    )
    assert check_strategy_policy_artifact_contract(wrong_hash_artifact, tau_policy_bundle=bundle).error == "tau_policy_bundle_hash_mismatch"

    wrong_version_artifact = StrategyPolicyArtifact(
        strategy=artifact.strategy,
        source_artifact_hash=artifact.source_artifact_hash,
        tau_policy_bundle_hash=artifact.tau_policy_bundle_hash,
        decision_model_version="other-model",
        signature=artifact.signature,
    )
    assert check_strategy_policy_artifact_contract(wrong_version_artifact, tau_policy_bundle=bundle).error == "decision_model_version_mismatch"

    invalid_sig_artifact = StrategyPolicyArtifact(
        strategy=artifact.strategy,
        source_artifact_hash=artifact.source_artifact_hash,
        tau_policy_bundle_hash=artifact.tau_policy_bundle_hash,
        decision_model_version=artifact.decision_model_version,
        signature="0xzz",
    )
    assert check_strategy_policy_artifact_contract(invalid_sig_artifact, tau_policy_bundle=bundle).error == "signature_invalid"
