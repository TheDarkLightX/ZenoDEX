from __future__ import annotations

from dataclasses import dataclass

from ...agents.policy_artifacts import (
    StrategyPolicyArtifact,
    TauPolicyBundle,
    verify_strategy_policy_artifact_signature,
)


@dataclass(frozen=True)
class StrategyPolicyArtifactContractResult:
    ok: bool
    strategy_hash_ok: bool
    owner_binding_ok: bool
    source_artifact_hash_ok: bool
    tau_policy_bundle_hash_ok: bool
    decision_model_version_ok: bool
    signature_present: bool
    signature_valid: bool
    error: str | None = None


def check_strategy_policy_artifact_contract(
    artifact: StrategyPolicyArtifact,
    *,
    tau_policy_bundle: TauPolicyBundle,
) -> StrategyPolicyArtifactContractResult:
    if not isinstance(artifact, StrategyPolicyArtifact):
        raise TypeError("artifact must be a StrategyPolicyArtifact")
    if not isinstance(tau_policy_bundle, TauPolicyBundle):
        raise TypeError("tau_policy_bundle must be a TauPolicyBundle")
    strategy_hash_ok = artifact.strategy.strategy_hash_hex() == tau_policy_bundle.strategy_hash
    owner_binding_ok = artifact.strategy.owner_pubkey == tau_policy_bundle.owner_pubkey
    source_artifact_hash_ok = artifact.source_artifact_hash == tau_policy_bundle.source_artifact_hash
    tau_policy_bundle_hash_ok = artifact.tau_policy_bundle_hash == tau_policy_bundle.tau_policy_bundle_hash_hex()
    decision_model_version_ok = artifact.decision_model_version == tau_policy_bundle.decision_model_version
    signature_present = artifact.signature is not None
    signature_valid = signature_present and verify_strategy_policy_artifact_signature(artifact)
    ok = all(
        (
            strategy_hash_ok,
            owner_binding_ok,
            source_artifact_hash_ok,
            tau_policy_bundle_hash_ok,
            decision_model_version_ok,
            signature_present,
            signature_valid,
        )
    )
    if not strategy_hash_ok:
        error = "strategy_hash_mismatch"
    elif not owner_binding_ok:
        error = "owner_binding_mismatch"
    elif not source_artifact_hash_ok:
        error = "source_artifact_hash_mismatch"
    elif not tau_policy_bundle_hash_ok:
        error = "tau_policy_bundle_hash_mismatch"
    elif not decision_model_version_ok:
        error = "decision_model_version_mismatch"
    elif not signature_present:
        error = "signature_missing"
    elif not signature_valid:
        error = "signature_invalid"
    else:
        error = None
    return StrategyPolicyArtifactContractResult(
        ok=ok,
        strategy_hash_ok=strategy_hash_ok,
        owner_binding_ok=owner_binding_ok,
        source_artifact_hash_ok=source_artifact_hash_ok,
        tau_policy_bundle_hash_ok=tau_policy_bundle_hash_ok,
        decision_model_version_ok=decision_model_version_ok,
        signature_present=signature_present,
        signature_valid=signature_valid,
        error=error,
    )
