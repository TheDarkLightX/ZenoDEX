from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from ...integration.autotrader_decision import StrategyCandidateSet


@dataclass(frozen=True)
class StrategyCandidateSetContractResult:
    ok: bool
    policy_artifact_hash_ok: bool
    tau_policy_bundle_hash_ok: bool
    observation_hash_ok: bool
    decision_model_version_ok: bool
    candidate_shape_ok: bool
    error: str | None = None


def check_strategy_candidate_set_contract(candidate_set: "StrategyCandidateSet") -> StrategyCandidateSetContractResult:
    from ...integration.autotrader_decision import DecisionCandidateKind, StrategyCandidateSet

    if not isinstance(candidate_set, StrategyCandidateSet):
        raise TypeError("candidate_set must be a StrategyCandidateSet")
    policy_artifact_hash_ok = bool(candidate_set.policy_artifact_hash)
    tau_policy_bundle_hash_ok = bool(candidate_set.tau_policy_bundle_hash)
    observation_hash_ok = bool(candidate_set.observation_hash)
    decision_model_version_ok = bool(candidate_set.decision_model_version)
    candidate_shape_ok = (
        len(candidate_set.candidates) == 2
        and candidate_set.candidates[0].candidate_index == 0
        and candidate_set.candidates[0].kind is DecisionCandidateKind.NO_OP
        and candidate_set.candidates[1].candidate_index == 1
        and candidate_set.candidates[1].kind is DecisionCandidateKind.EMIT_COMPILED_INTENT
    )
    ok = all(
        (
            policy_artifact_hash_ok,
            tau_policy_bundle_hash_ok,
            observation_hash_ok,
            decision_model_version_ok,
            candidate_shape_ok,
        )
    )
    if not policy_artifact_hash_ok:
        error = "policy_artifact_hash_missing"
    elif not tau_policy_bundle_hash_ok:
        error = "tau_policy_bundle_hash_missing"
    elif not observation_hash_ok:
        error = "observation_hash_missing"
    elif not decision_model_version_ok:
        error = "decision_model_version_missing"
    elif not candidate_shape_ok:
        error = "candidate_shape_invalid"
    else:
        error = None
    return StrategyCandidateSetContractResult(
        ok=ok,
        policy_artifact_hash_ok=policy_artifact_hash_ok,
        tau_policy_bundle_hash_ok=tau_policy_bundle_hash_ok,
        observation_hash_ok=observation_hash_ok,
        decision_model_version_ok=decision_model_version_ok,
        candidate_shape_ok=candidate_shape_ok,
        error=error,
    )
