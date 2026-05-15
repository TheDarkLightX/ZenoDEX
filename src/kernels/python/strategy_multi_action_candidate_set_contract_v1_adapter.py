from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from ...integration.autotrader_multiaction_decision import BoundedMultiActionCandidateSet


@dataclass(frozen=True)
class StrategyMultiActionCandidateSetContractResult:
    ok: bool
    policy_artifact_hash_ok: bool
    tau_policy_bundle_hash_ok: bool
    observation_hash_ok: bool
    decision_model_version_ok: bool
    candidate_count_ok: bool
    noop_head_ok: bool
    indices_contiguous_ok: bool
    kinds_unique_ok: bool
    candidate_shape_ok: bool
    error: str | None = None


def check_strategy_multi_action_candidate_set_contract(
    candidate_set: "BoundedMultiActionCandidateSet",
) -> StrategyMultiActionCandidateSetContractResult:
    from ...integration.autotrader_multiaction_decision import (
        BoundedMultiActionCandidateSet,
        MultiActionCandidateKind,
    )

    if not isinstance(candidate_set, BoundedMultiActionCandidateSet):
        raise TypeError("candidate_set must be a BoundedMultiActionCandidateSet")

    policy_artifact_hash_ok = bool(candidate_set.policy_artifact_hash)
    tau_policy_bundle_hash_ok = bool(candidate_set.tau_policy_bundle_hash)
    observation_hash_ok = bool(candidate_set.observation_hash)
    decision_model_version_ok = bool(candidate_set.decision_model_version)
    candidate_count_ok = len(candidate_set.candidates) >= 2
    noop_head_ok = (
        candidate_count_ok
        and candidate_set.candidates[0].candidate_index == 0
        and candidate_set.candidates[0].kind is MultiActionCandidateKind.NO_OP
        and bool(candidate_set.candidates[0].requested)
        and bool(candidate_set.candidates[0].admissible)
        and candidate_set.candidates[0].action_priority == 0
    )
    indices_contiguous_ok = all(
        candidate.candidate_index == expected_index
        for expected_index, candidate in enumerate(candidate_set.candidates)
    )
    kinds_unique_ok = len({candidate.kind for candidate in candidate_set.candidates}) == len(
        candidate_set.candidates
    )
    candidate_shape_ok = all(
        (
            candidate_count_ok,
            noop_head_ok,
            indices_contiguous_ok,
            kinds_unique_ok,
        )
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
    elif not candidate_count_ok:
        error = "candidate_count_invalid"
    elif not noop_head_ok:
        error = "noop_head_invalid"
    elif not indices_contiguous_ok:
        error = "candidate_indices_noncontiguous"
    elif not kinds_unique_ok:
        error = "candidate_kinds_not_unique"
    else:
        error = None
    return StrategyMultiActionCandidateSetContractResult(
        ok=ok,
        policy_artifact_hash_ok=policy_artifact_hash_ok,
        tau_policy_bundle_hash_ok=tau_policy_bundle_hash_ok,
        observation_hash_ok=observation_hash_ok,
        decision_model_version_ok=decision_model_version_ok,
        candidate_count_ok=candidate_count_ok,
        noop_head_ok=noop_head_ok,
        indices_contiguous_ok=indices_contiguous_ok,
        kinds_unique_ok=kinds_unique_ok,
        candidate_shape_ok=candidate_shape_ok,
        error=error,
    )
