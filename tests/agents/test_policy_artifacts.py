from __future__ import annotations

import pytest

import src.agents.policy_artifacts as policy_artifacts
from src.agents.policy_artifacts import (
    POLICY_ARTIFACT_SCHEMA,
    SOURCE_ARTIFACT_SCHEMA,
    TAU_POLICY_BUNDLE_SCHEMA,
    StrategyPolicyArtifact,
    StrategySourceArtifact,
    TauPolicyBundle,
    build_strategy_policy_artifact,
    build_strategy_source_artifact,
    build_tau_policy_bundle,
    sign_strategy_policy_artifact,
    strategy_policy_artifact_from_dict,
    strategy_source_artifact_from_dict,
    tau_policy_bundle_from_dict,
    verify_strategy_policy_artifact_signature,
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


def _strategy(owner_pubkey: str) -> StrategyIR:
    return StrategyIR(
        strategy_id="artifacts.1",
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


def test_policy_artifact_roundtrip_and_signature() -> None:
    privkey = 7
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _strategy(owner_pubkey)
    compile_receipt = build_compile_contract_tau_policy_receipt(strategy=strategy)
    source_artifact = build_strategy_source_artifact(
        strategy=strategy,
        source_form="kv",
        source_text="template: dca",
    )
    bundle = build_tau_policy_bundle(
        strategy=strategy,
        compile_contract_tau_receipt=compile_receipt.to_dict(),
        source_artifact=source_artifact,
    )
    artifact = build_strategy_policy_artifact(
        strategy=strategy,
        tau_policy_bundle=bundle,
        source_artifact=source_artifact,
    )
    signed = sign_strategy_policy_artifact(artifact, privkey=privkey)

    assert source_artifact.to_dict()["schema"] == SOURCE_ARTIFACT_SCHEMA
    assert bundle.to_dict()["schema"] == TAU_POLICY_BUNDLE_SCHEMA
    assert bundle.to_dict()["evidence_class"] == "O3"
    assert bundle.required_spec_ids == AUTOTRADER_TAU_POLICY_SPECS
    assert signed.to_dict()["schema"] == POLICY_ARTIFACT_SCHEMA
    assert signed.signature is not None
    assert verify_strategy_policy_artifact_signature(signed) is True

    loaded_source = strategy_source_artifact_from_dict(source_artifact.to_dict())
    loaded_bundle = tau_policy_bundle_from_dict(bundle.to_dict())
    loaded_artifact = strategy_policy_artifact_from_dict(signed.to_dict())
    assert loaded_source.source_artifact_hash_hex() == source_artifact.source_artifact_hash_hex()
    assert loaded_bundle.tau_policy_bundle_hash_hex() == bundle.tau_policy_bundle_hash_hex()
    assert loaded_artifact.policy_artifact_hash_hex() == signed.policy_artifact_hash_hex()


def test_policy_artifact_sign_rejects_wrong_owner() -> None:
    strategy = _strategy("0x" + bls_pubkey_hex_from_privkey(11))
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

    try:
        sign_strategy_policy_artifact(artifact, privkey=12)
    except ValueError as exc:
        assert "signer pubkey does not match artifact owner" in str(exc)
    else:  # pragma: no cover
        raise AssertionError("expected signer mismatch")


def test_policy_artifact_internal_validator_and_privkey_edges(monkeypatch: pytest.MonkeyPatch) -> None:
    with pytest.raises(TypeError, match="mapping must be an object"):
        policy_artifacts._require_mapping([], name="mapping")
    with pytest.raises(TypeError, match="text must be a string"):
        policy_artifacts._require_text(7, name="text")
    with pytest.raises(ValueError, match="text must be non-empty"):
        policy_artifacts._require_text("   ", name="text")
    assert policy_artifacts._require_bool(True, name="flag") is True
    with pytest.raises(TypeError, match="flag must be a bool"):
        policy_artifacts._require_bool("true", name="flag")

    assert policy_artifacts._parse_privkey_to_int(b"\x01" * 32) > 0
    assert policy_artifacts._parse_privkey_to_int(bytearray(b"\x02" * 32)) > 0
    assert policy_artifacts._parse_privkey_to_int("3") == 3
    assert policy_artifacts._parse_privkey_to_int("0x" + "04" * 32) > 0
    with pytest.raises(ValueError, match="privkey bytes must be length 32"):
        policy_artifacts._parse_privkey_to_int(b"\x01")
    with pytest.raises(ValueError, match="privkey must be non-empty"):
        policy_artifacts._parse_privkey_to_int("   ")
    with pytest.raises(ValueError, match="privkey must be 32-byte hex or a positive integer string"):
        policy_artifacts._parse_privkey_to_int("not-a-key")
    with pytest.raises(TypeError, match="privkey must be str\\|int\\|bytes"):
        policy_artifacts._parse_privkey_to_int(object())
    with pytest.raises(ValueError, match="privkey must be positive"):
        policy_artifacts._parse_privkey_to_int(0)

    monkeypatch.setattr(policy_artifacts, "_BLS12_381_CURVE_ORDER", 5)
    with pytest.raises(ValueError, match="privkey out of range"):
        policy_artifacts._parse_privkey_to_int(5)

    monkeypatch.setattr(policy_artifacts, "_BLS_AVAILABLE", False)
    with pytest.raises(ValueError, match="py_ecc.bls is required"):
        policy_artifacts._require_bls()


def test_policy_artifact_constructor_and_loader_fail_closed_edges(monkeypatch: pytest.MonkeyPatch) -> None:
    privkey = 29
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = _strategy(owner_pubkey)
    compile_receipt = build_compile_contract_tau_policy_receipt(strategy=strategy).to_dict()

    source_artifact = build_strategy_source_artifact(strategy=strategy, source_form="kv")
    witness_receipt = build_compilation_witness_tau_policy_receipt(
        strategy=strategy,
        source_artifact=source_artifact,
        compile_contract_tau_receipt=compile_receipt,
    ).to_dict()
    bundle = TauPolicyBundle(
        strategy_hash=strategy.strategy_hash_hex(),
        owner_pubkey=owner_pubkey,
        source_artifact_hash=source_artifact.source_artifact_hash_hex(),
        required_spec_ids=AUTOTRADER_TAU_POLICY_SPECS + (AUTOTRADER_TAU_POLICY_SPECS[0],),
        compile_contract_tau_receipt=compile_receipt,
        compilation_witness_tau_receipt=witness_receipt,
    )
    assert bundle.required_spec_ids == AUTOTRADER_TAU_POLICY_SPECS

    with pytest.raises(ValueError, match="required_spec_ids must equal the canonical autotrader Tau bundle"):
        TauPolicyBundle(
            strategy_hash=strategy.strategy_hash_hex(),
            owner_pubkey=owner_pubkey,
            source_artifact_hash=source_artifact.source_artifact_hash_hex(),
            required_spec_ids=("bad.spec",),
            compile_contract_tau_receipt=compile_receipt,
            compilation_witness_tau_receipt=witness_receipt,
        )
    with pytest.raises(TypeError, match="compile_contract_tau_receipt must be an object"):
        TauPolicyBundle(
            strategy_hash=strategy.strategy_hash_hex(),
            owner_pubkey=owner_pubkey,
            source_artifact_hash=source_artifact.source_artifact_hash_hex(),
            required_spec_ids=AUTOTRADER_TAU_POLICY_SPECS,
            compile_contract_tau_receipt=[],
            compilation_witness_tau_receipt=witness_receipt,
        )
    with pytest.raises(TypeError, match="compilation_witness_tau_receipt must be an object"):
        TauPolicyBundle(
            strategy_hash=strategy.strategy_hash_hex(),
            owner_pubkey=owner_pubkey,
            source_artifact_hash=source_artifact.source_artifact_hash_hex(),
            required_spec_ids=AUTOTRADER_TAU_POLICY_SPECS,
            compile_contract_tau_receipt=compile_receipt,
            compilation_witness_tau_receipt=[],
        )
    with pytest.raises(ValueError, match="source_text_hash must be non-empty"):
        StrategySourceArtifact(source_form="kv", strategy=strategy, source_text_hash=" ")
    with pytest.raises(TypeError, match="strategy must be a StrategyIR"):
        StrategyPolicyArtifact(
            strategy="bad",  # type: ignore[arg-type]
            source_artifact_hash=source_artifact.source_artifact_hash_hex(),
            tau_policy_bundle_hash=bundle.tau_policy_bundle_hash_hex(),
        )
    with pytest.raises(ValueError, match="signature must be non-empty"):
        StrategyPolicyArtifact(
            strategy=strategy,
            source_artifact_hash=source_artifact.source_artifact_hash_hex(),
            tau_policy_bundle_hash=bundle.tau_policy_bundle_hash_hex(),
            signature=" ",
        )
    with pytest.raises(TypeError, match="strategy must be a StrategyIR"):
        build_tau_policy_bundle(
            strategy="bad",  # type: ignore[arg-type]
            compile_contract_tau_receipt=compile_receipt,
        )
    with pytest.raises(TypeError, match="tau_policy_bundle must be a TauPolicyBundle"):
        build_strategy_policy_artifact(
            strategy=strategy,
            tau_policy_bundle="bad",  # type: ignore[arg-type]
        )

    wrong_hash_bundle = TauPolicyBundle(
        strategy_hash="0xdead",
        owner_pubkey=owner_pubkey,
        source_artifact_hash=source_artifact.source_artifact_hash_hex(),
        required_spec_ids=AUTOTRADER_TAU_POLICY_SPECS,
        compile_contract_tau_receipt=compile_receipt,
        compilation_witness_tau_receipt=witness_receipt,
    )
    with pytest.raises(ValueError, match="tau policy bundle strategy hash mismatch"):
        build_strategy_policy_artifact(strategy=strategy, tau_policy_bundle=wrong_hash_bundle)

    wrong_owner_bundle = TauPolicyBundle(
        strategy_hash=strategy.strategy_hash_hex(),
        owner_pubkey="other.owner",
        source_artifact_hash=source_artifact.source_artifact_hash_hex(),
        required_spec_ids=AUTOTRADER_TAU_POLICY_SPECS,
        compile_contract_tau_receipt=compile_receipt,
        compilation_witness_tau_receipt=witness_receipt,
    )
    with pytest.raises(ValueError, match="tau policy bundle owner mismatch"):
        build_strategy_policy_artifact(strategy=strategy, tau_policy_bundle=wrong_owner_bundle)

    wrong_version_bundle = TauPolicyBundle(
        strategy_hash=strategy.strategy_hash_hex(),
        owner_pubkey=owner_pubkey,
        source_artifact_hash=source_artifact.source_artifact_hash_hex(),
        required_spec_ids=AUTOTRADER_TAU_POLICY_SPECS,
        compile_contract_tau_receipt=compile_receipt,
        compilation_witness_tau_receipt=witness_receipt,
        decision_model_version="other-model",
    )
    with pytest.raises(ValueError, match="decision model version mismatch"):
        build_strategy_policy_artifact(strategy=strategy, tau_policy_bundle=wrong_version_bundle)

    unsigned = build_strategy_policy_artifact(
        strategy=strategy,
        tau_policy_bundle=bundle,
        source_artifact=source_artifact,
    )
    signed = sign_strategy_policy_artifact(unsigned, privkey=privkey)

    with pytest.raises(TypeError, match="artifact must be a StrategyPolicyArtifact"):
        sign_strategy_policy_artifact("bad", privkey=privkey)  # type: ignore[arg-type]

    monkeypatch.setattr(policy_artifacts, "_BLS_AVAILABLE", False)
    with pytest.raises(ValueError, match="py_ecc.bls is required"):
        sign_strategy_policy_artifact(unsigned, privkey=privkey)
    assert verify_strategy_policy_artifact_signature(signed) is False

    monkeypatch.setattr(policy_artifacts, "_BLS_AVAILABLE", True)
    invalid_sig = StrategyPolicyArtifact(
        strategy=signed.strategy,
        source_artifact_hash=signed.source_artifact_hash,
        tau_policy_bundle_hash=signed.tau_policy_bundle_hash,
        decision_model_version=signed.decision_model_version,
        signature="0xzz",
    )
    assert verify_strategy_policy_artifact_signature(unsigned) is False
    assert verify_strategy_policy_artifact_signature(invalid_sig) is False

    bundle_doc = bundle.to_dict()
    bad_schema_bundle_doc = dict(bundle_doc, schema="bad.schema")
    with pytest.raises(ValueError, match="unsupported tau policy bundle schema"):
        tau_policy_bundle_from_dict(bad_schema_bundle_doc)
    bad_hash_bundle_doc = dict(bundle_doc, tau_policy_bundle_hash="0xdead")
    with pytest.raises(ValueError, match="tau policy bundle hash mismatch"):
        tau_policy_bundle_from_dict(bad_hash_bundle_doc)

    source_doc = source_artifact.to_dict()
    bad_schema_source_doc = dict(source_doc, schema="bad.schema")
    with pytest.raises(ValueError, match="unsupported source artifact schema"):
        strategy_source_artifact_from_dict(bad_schema_source_doc)
    bad_strategy_hash_source_doc = dict(source_doc, strategy_hash="0xdead")
    with pytest.raises(ValueError, match="source artifact strategy_hash mismatch"):
        strategy_source_artifact_from_dict(bad_strategy_hash_source_doc)
    bad_owner_source_doc = dict(source_doc, owner_pubkey="other.owner")
    with pytest.raises(ValueError, match="source artifact owner_pubkey mismatch"):
        strategy_source_artifact_from_dict(bad_owner_source_doc)
    bad_source_hash_doc = dict(source_doc, source_artifact_hash="0xdead")
    with pytest.raises(ValueError, match="source artifact hash mismatch"):
        strategy_source_artifact_from_dict(bad_source_hash_doc)

    artifact_doc = signed.to_dict()
    bad_schema_artifact_doc = dict(artifact_doc, schema="bad.schema")
    with pytest.raises(ValueError, match="unsupported policy artifact schema"):
        strategy_policy_artifact_from_dict(bad_schema_artifact_doc)
    bad_strategy_hash_doc = dict(artifact_doc, strategy_hash="0xdead")
    with pytest.raises(ValueError, match="policy artifact strategy_hash mismatch"):
        strategy_policy_artifact_from_dict(bad_strategy_hash_doc)
    bad_owner_doc = dict(artifact_doc, owner_pubkey="other.owner")
    with pytest.raises(ValueError, match="policy artifact owner_pubkey mismatch"):
        strategy_policy_artifact_from_dict(bad_owner_doc)
    bad_source_hash_doc = dict(artifact_doc, source_artifact_hash="0xdead")
    with pytest.raises(ValueError, match="policy artifact hash mismatch"):
        strategy_policy_artifact_from_dict(bad_source_hash_doc)
    bad_artifact_hash_doc = dict(artifact_doc, policy_artifact_hash="0xdead")
    with pytest.raises(ValueError, match="policy artifact hash mismatch"):
        strategy_policy_artifact_from_dict(bad_artifact_hash_doc)


def test_source_artifact_and_bundle_builders_cover_default_and_fail_closed_paths() -> None:
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(31)
    strategy = _strategy(owner_pubkey)
    compile_receipt = build_compile_contract_tau_policy_receipt(strategy=strategy).to_dict()

    with pytest.raises(TypeError, match="strategy must be a StrategyIR"):
        StrategySourceArtifact(source_form="kv", strategy="bad")  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="strategy must be a StrategyIR"):
        build_strategy_source_artifact(strategy="bad", source_form="kv")  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="source_text must be a string"):
        build_strategy_source_artifact(
            strategy=strategy,
            source_form="kv",
            source_text=7,  # type: ignore[arg-type]
        )

    explicit_source = build_strategy_source_artifact(
        strategy=strategy,
        source_form="sentence",
        source_text="dca 100 zUSD into BTC every 4 epochs",
    )
    explicit_witness = build_compilation_witness_tau_policy_receipt(
        strategy=strategy,
        source_artifact=explicit_source,
        compile_contract_tau_receipt=compile_receipt,
    ).to_dict()

    default_bundle = build_tau_policy_bundle(
        strategy=strategy,
        compile_contract_tau_receipt=compile_receipt,
        compilation_witness_tau_receipt=explicit_witness,
    )
    assert default_bundle.source_artifact_hash
    assert default_bundle.compilation_witness_tau_receipt == explicit_witness

    with pytest.raises(TypeError, match="source_artifact must be a StrategySourceArtifact"):
        build_tau_policy_bundle(
            strategy=strategy,
            compile_contract_tau_receipt=compile_receipt,
            source_artifact="bad",  # type: ignore[arg-type]
        )

    mismatched_strategy = _strategy(owner_pubkey)
    object.__setattr__(
        mismatched_strategy,
        "template_params",
        {
            "fixed_order_size": 100,
            "cadence_epochs": 8,
            "asset_in": "zUSD",
            "asset_out": "BTC",
        },
    )
    mismatched_source = build_strategy_source_artifact(
        strategy=mismatched_strategy,
        source_form="kv",
    )
    with pytest.raises(ValueError, match="source artifact strategy hash mismatch"):
        build_tau_policy_bundle(
            strategy=strategy,
            compile_contract_tau_receipt=compile_receipt,
            source_artifact=mismatched_source,
        )

    artifact_without_source = build_strategy_policy_artifact(
        strategy=strategy,
        tau_policy_bundle=default_bundle,
    )
    assert artifact_without_source.source_artifact_hash == default_bundle.source_artifact_hash

    with pytest.raises(TypeError, match="source_artifact must be a StrategySourceArtifact"):
        build_strategy_policy_artifact(
            strategy=strategy,
            tau_policy_bundle=default_bundle,
            source_artifact="bad",  # type: ignore[arg-type]
        )
    with pytest.raises(ValueError, match="source artifact hash mismatch"):
        build_strategy_policy_artifact(
            strategy=strategy,
            tau_policy_bundle=default_bundle,
            source_artifact=explicit_source,
        )
