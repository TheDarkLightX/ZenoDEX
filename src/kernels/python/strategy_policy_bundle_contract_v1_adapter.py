from __future__ import annotations

from dataclasses import dataclass

from ...agents.policy_artifacts import TauPolicyBundle
from ...agents.strategy_ir import AUTOTRADER_TAU_POLICY_SPECS


@dataclass(frozen=True)
class StrategyPolicyBundleContractResult:
    ok: bool
    strategy_hash_ok: bool
    owner_binding_ok: bool
    source_artifact_hash_ok: bool
    canonical_specs_ok: bool
    compile_contract_ok: bool
    compilation_witness_ok: bool
    decision_model_version_ok: bool
    error: str | None = None


def check_strategy_policy_bundle_contract(bundle: TauPolicyBundle) -> StrategyPolicyBundleContractResult:
    if not isinstance(bundle, TauPolicyBundle):
        raise TypeError("bundle must be a TauPolicyBundle")
    strategy_hash_ok = bool(bundle.strategy_hash)
    owner_binding_ok = bool(bundle.owner_pubkey)
    source_artifact_hash_ok = bool(bundle.source_artifact_hash)
    canonical_specs_ok = bundle.required_spec_ids == AUTOTRADER_TAU_POLICY_SPECS
    receipt = dict(bundle.compile_contract_tau_receipt)
    compile_contract_ok = bool(receipt.get("expected_ok")) and receipt.get("spec_id") == "autotrader_compile_contract_v1"
    witness_receipt = dict(bundle.compilation_witness_tau_receipt)
    compilation_witness_ok = (
        bool(witness_receipt.get("expected_ok"))
        and witness_receipt.get("spec_id") == "autotrader_compilation_witness_v1"
    )
    decision_model_version_ok = bool(bundle.decision_model_version)
    ok = all(
        (
            strategy_hash_ok,
            owner_binding_ok,
            source_artifact_hash_ok,
            canonical_specs_ok,
            compile_contract_ok,
            compilation_witness_ok,
            decision_model_version_ok,
        )
    )
    if not strategy_hash_ok:
        error = "strategy_hash_missing"
    elif not owner_binding_ok:
        error = "owner_binding_missing"
    elif not source_artifact_hash_ok:
        error = "source_artifact_hash_missing"
    elif not canonical_specs_ok:
        error = "canonical_specs_invalid"
    elif not compile_contract_ok:
        error = "compile_contract_tau_receipt_invalid"
    elif not compilation_witness_ok:
        error = "compilation_witness_tau_receipt_invalid"
    elif not decision_model_version_ok:
        error = "decision_model_version_missing"
    else:
        error = None
    return StrategyPolicyBundleContractResult(
        ok=ok,
        strategy_hash_ok=strategy_hash_ok,
        owner_binding_ok=owner_binding_ok,
        source_artifact_hash_ok=source_artifact_hash_ok,
        canonical_specs_ok=canonical_specs_ok,
        compile_contract_ok=compile_contract_ok,
        compilation_witness_ok=compilation_witness_ok,
        decision_model_version_ok=decision_model_version_ok,
        error=error,
    )
