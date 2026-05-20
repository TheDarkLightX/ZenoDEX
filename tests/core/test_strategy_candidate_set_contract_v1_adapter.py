from __future__ import annotations

import pytest

from src.integration.autotrader_decision import (
    DecisionCandidate,
    DecisionCandidateKind,
    StrategyCandidateSet,
)
from src.kernels.python.strategy_candidate_set_contract_v1_adapter import (
    check_strategy_candidate_set_contract,
)


def _candidate_set(
    *,
    policy_artifact_hash: str = "artifact.hash",
    tau_policy_bundle_hash: str = "bundle.hash",
    observation_hash: str = "obs.hash",
    decision_model_version: str = "autotrader-binary-v1",
    candidates: tuple[DecisionCandidate, ...] | None = None,
) -> StrategyCandidateSet:
    if candidates is None:
        candidates = (
            DecisionCandidate(0, DecisionCandidateKind.NO_OP, True, True, 0),
            DecisionCandidate(1, DecisionCandidateKind.EMIT_COMPILED_INTENT, True, True, 1),
        )
    candidate_set = object.__new__(StrategyCandidateSet)
    object.__setattr__(candidate_set, "policy_artifact_hash", policy_artifact_hash)
    object.__setattr__(candidate_set, "tau_policy_bundle_hash", tau_policy_bundle_hash)
    object.__setattr__(candidate_set, "observation_hash", observation_hash)
    object.__setattr__(candidate_set, "decision_model_version", decision_model_version)
    object.__setattr__(candidate_set, "candidates", candidates)
    return candidate_set


def test_strategy_candidate_set_contract_accepts_and_fail_closes() -> None:
    assert check_strategy_candidate_set_contract(_candidate_set()).ok is True

    with pytest.raises(TypeError, match="candidate_set must be a StrategyCandidateSet"):
        check_strategy_candidate_set_contract("bad")  # type: ignore[arg-type]

    assert check_strategy_candidate_set_contract(_candidate_set(policy_artifact_hash="")).error == "policy_artifact_hash_missing"
    assert check_strategy_candidate_set_contract(_candidate_set(policy_artifact_hash="a", tau_policy_bundle_hash="")).error == "tau_policy_bundle_hash_missing"
    assert check_strategy_candidate_set_contract(_candidate_set(policy_artifact_hash="a", tau_policy_bundle_hash="b", observation_hash="")).error == "observation_hash_missing"
    assert check_strategy_candidate_set_contract(_candidate_set(policy_artifact_hash="a", tau_policy_bundle_hash="b", observation_hash="c", decision_model_version="")).error == "decision_model_version_missing"
    assert (
        check_strategy_candidate_set_contract(
            _candidate_set(
                candidates=(
                    DecisionCandidate(0, DecisionCandidateKind.NO_OP, True, True, 0),
                    DecisionCandidate(2, DecisionCandidateKind.EMIT_COMPILED_INTENT, True, True, 1),
                )
            )
        ).error
        == "candidate_shape_invalid"
    )
