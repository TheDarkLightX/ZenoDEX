from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any

from ..agents.policy_artifacts import StrategyPolicyArtifact, TauPolicyBundle
from ..kernels.python.strategy_candidate_set_contract_v1_adapter import (
    check_strategy_candidate_set_contract,
)
from ..kernels.python.strategy_decision_kernel_v1_adapter import check_strategy_decision_kernel
from ..kernels.python.strategy_kill_switch_guard_v1_adapter import check_strategy_kill_switch_guard
from ..state.canonical import canonical_json_bytes, sha256_hex
from .autotrader_signals import AutoTraderObservationPacket
from .tau_witness import build_argmax_stream_certificate_v1_step

CANDIDATE_SET_SCHEMA = "zenodex/strategy-candidate-set/v1"
DECISION_CERTIFICATE_SCHEMA = "zenodex/strategy-decision/v1"
DEFAULT_DECISION_MODEL_VERSION = "autotrader-binary-v1"

class DecisionCandidateKind(Enum):
    NO_OP = "no_op"
    EMIT_COMPILED_INTENT = "emit_compiled_intent"


@dataclass(frozen=True)
class DecisionCandidate:
    candidate_index: int
    kind: DecisionCandidateKind
    requested: bool
    admissible: bool
    candidate_key: int

    def __post_init__(self) -> None:
        if not isinstance(self.candidate_index, int) or isinstance(self.candidate_index, bool):
            raise TypeError("candidate_index must be an int")
        if self.candidate_index < 0 or self.candidate_index > 0xFFFFFFFF:
            raise ValueError(f"candidate_index out of range: {self.candidate_index}")
        if not isinstance(self.kind, DecisionCandidateKind):
            raise TypeError("kind must be a DecisionCandidateKind")
        if not isinstance(self.requested, bool):
            raise TypeError("requested must be a bool")
        if not isinstance(self.admissible, bool):
            raise TypeError("admissible must be a bool")
        if not isinstance(self.candidate_key, int) or isinstance(self.candidate_key, bool):
            raise TypeError("candidate_key must be an int")
        if self.candidate_key < 0 or self.candidate_key > 0xFFFFFFFFFFFFFFFF:
            raise ValueError(f"candidate_key out of range: {self.candidate_key}")

    def to_dict(self) -> dict[str, Any]:
        return {
            "candidate_index": int(self.candidate_index),
            "kind": self.kind.value,
            "requested": bool(self.requested),
            "admissible": bool(self.admissible),
            "candidate_key": int(self.candidate_key),
        }


@dataclass(frozen=True)
class StrategyCandidateSet:
    policy_artifact_hash: str
    tau_policy_bundle_hash: str
    observation_hash: str
    decision_model_version: str
    candidates: tuple[DecisionCandidate, ...]

    def __post_init__(self) -> None:
        for name in ("policy_artifact_hash", "tau_policy_bundle_hash", "observation_hash", "decision_model_version"):
            value = getattr(self, name)
            if not isinstance(value, str) or not value.strip():
                raise ValueError(f"{name} must be a non-empty string")
        if len(self.candidates) != 2:
            raise ValueError("candidate set must contain exactly two candidates")
        if self.candidates[0].kind is not DecisionCandidateKind.NO_OP or self.candidates[0].candidate_index != 0:
            raise ValueError("candidate 0 must be NO_OP")
        if self.candidates[1].kind is not DecisionCandidateKind.EMIT_COMPILED_INTENT or self.candidates[1].candidate_index != 1:
            raise ValueError("candidate 1 must be EMIT_COMPILED_INTENT")

    def to_unsigned_dict(self) -> dict[str, Any]:
        return {
            "schema": CANDIDATE_SET_SCHEMA,
            "policy_artifact_hash": self.policy_artifact_hash,
            "tau_policy_bundle_hash": self.tau_policy_bundle_hash,
            "observation_hash": self.observation_hash,
            "decision_model_version": self.decision_model_version,
            "candidates": [candidate.to_dict() for candidate in self.candidates],
        }

    def to_dict(self) -> dict[str, Any]:
        payload = self.to_unsigned_dict()
        payload["candidate_set_hash"] = self.candidate_set_hash_hex()
        return payload

    def candidate_set_hash_hex(self) -> str:
        return sha256_hex(canonical_json_bytes(self.to_unsigned_dict()))


@dataclass(frozen=True)
class StrategyDecisionCertificate:
    policy_artifact_hash: str
    tau_policy_bundle_hash: str
    observation_hash: str
    candidate_set_hash: str
    decision_model_version: str
    winner_index: int
    winner_kind: DecisionCandidateKind
    winner_key: int
    argmax_steps: tuple[dict[str, int], ...]
    kill_switch_active: bool

    def __post_init__(self) -> None:
        for name in (
            "policy_artifact_hash",
            "tau_policy_bundle_hash",
            "observation_hash",
            "candidate_set_hash",
            "decision_model_version",
        ):
            value = getattr(self, name)
            if not isinstance(value, str) or not value.strip():
                raise ValueError(f"{name} must be a non-empty string")
        if not isinstance(self.winner_index, int) or isinstance(self.winner_index, bool):
            raise TypeError("winner_index must be an int")
        if self.winner_index not in (0, 1):
            raise ValueError(f"winner_index must be 0 or 1: {self.winner_index}")
        if not isinstance(self.winner_kind, DecisionCandidateKind):
            raise TypeError("winner_kind must be a DecisionCandidateKind")
        if not isinstance(self.winner_key, int) or isinstance(self.winner_key, bool):
            raise TypeError("winner_key must be an int")
        if self.winner_key < 0 or self.winner_key > 0xFFFFFFFFFFFFFFFF:
            raise ValueError(f"winner_key out of range: {self.winner_key}")
        if not isinstance(self.kill_switch_active, bool):
            raise TypeError("kill_switch_active must be a bool")
        if not self.argmax_steps:
            raise ValueError("argmax_steps must be non-empty")

    def to_unsigned_dict(self) -> dict[str, Any]:
        return {
            "schema": DECISION_CERTIFICATE_SCHEMA,
            "policy_artifact_hash": self.policy_artifact_hash,
            "tau_policy_bundle_hash": self.tau_policy_bundle_hash,
            "observation_hash": self.observation_hash,
            "candidate_set_hash": self.candidate_set_hash,
            "decision_model_version": self.decision_model_version,
            "winner_index": int(self.winner_index),
            "winner_kind": self.winner_kind.value,
            "winner_key": int(self.winner_key),
            "argmax_steps": [dict(step) for step in self.argmax_steps],
            "kill_switch_active": bool(self.kill_switch_active),
        }

    def to_dict(self) -> dict[str, Any]:
        payload = self.to_unsigned_dict()
        payload["decision_hash"] = self.decision_hash_hex()
        return payload

    def decision_hash_hex(self) -> str:
        return sha256_hex(canonical_json_bytes(self.to_unsigned_dict()))


def observation_hash_hex(packet: AutoTraderObservationPacket) -> str:
    if not isinstance(packet, AutoTraderObservationPacket):
        raise TypeError("packet must be an AutoTraderObservationPacket")
    return sha256_hex(canonical_json_bytes(packet.to_dict()))


def build_strategy_candidate_set(
    *,
    policy_artifact: StrategyPolicyArtifact,
    tau_policy_bundle: TauPolicyBundle,
    observation_packet: AutoTraderObservationPacket,
    emit_requested: bool,
    emit_admissible: bool,
) -> StrategyCandidateSet:
    if not isinstance(policy_artifact, StrategyPolicyArtifact):
        raise TypeError("policy_artifact must be a StrategyPolicyArtifact")
    if not isinstance(tau_policy_bundle, TauPolicyBundle):
        raise TypeError("tau_policy_bundle must be a TauPolicyBundle")
    observation_hash = observation_hash_hex(observation_packet)
    candidates = (
        DecisionCandidate(
            candidate_index=0,
            kind=DecisionCandidateKind.NO_OP,
            requested=True,
            admissible=True,
            candidate_key=0,
        ),
        DecisionCandidate(
            candidate_index=1,
            kind=DecisionCandidateKind.EMIT_COMPILED_INTENT,
            requested=bool(emit_requested),
            admissible=bool(emit_admissible),
            candidate_key=1 if emit_requested and emit_admissible else 0,
        ),
    )
    candidate_set = StrategyCandidateSet(
        policy_artifact_hash=policy_artifact.policy_artifact_hash_hex(),
        tau_policy_bundle_hash=tau_policy_bundle.tau_policy_bundle_hash_hex(),
        observation_hash=observation_hash,
        decision_model_version=policy_artifact.decision_model_version,
        candidates=candidates,
    )
    contract = check_strategy_candidate_set_contract(candidate_set)
    if not contract.ok:
        raise ValueError(f"candidate set contract rejected: {contract.error}")
    return candidate_set


def build_strategy_decision_certificate(
    *,
    candidate_set: StrategyCandidateSet,
    kill_switch_active: bool,
) -> StrategyDecisionCertificate:
    if not isinstance(candidate_set, StrategyCandidateSet):
        raise TypeError("candidate_set must be a StrategyCandidateSet")
    kill_switch = check_strategy_kill_switch_guard(
        kill_switch_enabled=True,
        kill_switch_active=kill_switch_active,
    )
    emit_requested = candidate_set.candidates[1].requested
    emit_admissible = candidate_set.candidates[1].admissible and kill_switch.ok
    decision = check_strategy_decision_kernel(
        emit_requested=emit_requested,
        emit_admissible=emit_admissible,
    )
    binding_ok = int(
        derive_strategy_decision_binding_ok(
            candidate_set=candidate_set,
            winner_index=decision.winner_index,
            winner_key=decision.winner_key,
            kill_switch_active=kill_switch_active,
        )
    )
    argmax_steps = tuple(
        build_argmax_stream_certificate_v1_step(
            winner_key=decision.winner_key,
            winner_index=decision.winner_index,
            cand_key=candidate.candidate_key if candidate.kind is DecisionCandidateKind.NO_OP else (1 if emit_requested and emit_admissible else 0),
            cand_index=candidate.candidate_index,
            binding_ok=binding_ok,
        )
        for candidate in candidate_set.candidates
    )
    return StrategyDecisionCertificate(
        policy_artifact_hash=candidate_set.policy_artifact_hash,
        tau_policy_bundle_hash=candidate_set.tau_policy_bundle_hash,
        observation_hash=candidate_set.observation_hash,
        candidate_set_hash=candidate_set.candidate_set_hash_hex(),
        decision_model_version=candidate_set.decision_model_version,
        winner_index=decision.winner_index,
        winner_kind=DecisionCandidateKind.NO_OP if decision.winner_index == 0 else DecisionCandidateKind.EMIT_COMPILED_INTENT,
        winner_key=decision.winner_key,
        argmax_steps=argmax_steps,
        kill_switch_active=bool(kill_switch_active),
    )


def derive_strategy_decision_binding_ok(
    *,
    candidate_set: StrategyCandidateSet,
    winner_index: int,
    winner_key: int,
    kill_switch_active: bool,
) -> bool:
    if not isinstance(candidate_set, StrategyCandidateSet):
        raise TypeError("candidate_set must be a StrategyCandidateSet")
    if not isinstance(winner_index, int) or isinstance(winner_index, bool):
        raise TypeError("winner_index must be an int")
    if not isinstance(winner_key, int) or isinstance(winner_key, bool):
        raise TypeError("winner_key must be an int")
    if not isinstance(kill_switch_active, bool):
        raise TypeError("kill_switch_active must be a bool")

    contract = check_strategy_candidate_set_contract(candidate_set)
    if not contract.ok:
        return False
    noop_candidate, emit_candidate = candidate_set.candidates
    if noop_candidate.candidate_key != 0:
        return False
    expected_emit_key = 1 if emit_candidate.requested and emit_candidate.admissible else 0
    if emit_candidate.candidate_key != expected_emit_key:
        return False

    kill_switch = check_strategy_kill_switch_guard(
        kill_switch_enabled=True,
        kill_switch_active=kill_switch_active,
    )
    decision = check_strategy_decision_kernel(
        emit_requested=emit_candidate.requested,
        emit_admissible=emit_candidate.admissible and kill_switch.ok,
    )
    return (
        decision.ok
        and winner_index == decision.winner_index
        and winner_key == decision.winner_key
        and candidate_set.candidate_set_hash_hex() == sha256_hex(canonical_json_bytes(candidate_set.to_unsigned_dict()))
    )


def verify_strategy_decision_certificate(
    *,
    candidate_set: StrategyCandidateSet,
    certificate: StrategyDecisionCertificate,
    expected_kill_switch_active: bool | None = None,
) -> tuple[bool, str | None]:
    if not isinstance(candidate_set, StrategyCandidateSet):
        raise TypeError("candidate_set must be a StrategyCandidateSet")
    if not isinstance(certificate, StrategyDecisionCertificate):
        raise TypeError("certificate must be a StrategyDecisionCertificate")
    if expected_kill_switch_active is not None and not isinstance(expected_kill_switch_active, bool):
        raise TypeError("expected_kill_switch_active must be a bool when provided")

    effective_kill_switch_active = (
        expected_kill_switch_active if expected_kill_switch_active is not None else certificate.kill_switch_active
    )
    expected = build_strategy_decision_certificate(
        candidate_set=candidate_set,
        kill_switch_active=effective_kill_switch_active,
    )

    if expected_kill_switch_active is not None and certificate.kill_switch_active != expected_kill_switch_active:
        return False, "kill_switch_active mismatch"
    for field_name in (
        "policy_artifact_hash",
        "tau_policy_bundle_hash",
        "observation_hash",
        "candidate_set_hash",
        "decision_model_version",
    ):
        if getattr(certificate, field_name) != getattr(expected, field_name):
            return False, f"{field_name} mismatch"
    if certificate.winner_index != expected.winner_index:
        return False, "winner_index mismatch"
    if certificate.winner_kind is not expected.winner_kind:
        return False, "winner_kind mismatch"
    if certificate.winner_key != expected.winner_key:
        return False, "winner_key mismatch"
    if certificate.argmax_steps != expected.argmax_steps:
        return False, "argmax_steps mismatch"
    return True, None


def verify_strategy_candidate_set_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "candidate set payload must be an object"
    if payload.get("schema") != CANDIDATE_SET_SCHEMA:
        return False, "unsupported candidate set schema"
    expected_hash = payload.get("candidate_set_hash")
    unsigned_payload = {key: value for key, value in payload.items() if key != "candidate_set_hash"}
    if expected_hash != sha256_hex(canonical_json_bytes(unsigned_payload)):
        return False, "candidate_set_hash mismatch"
    candidates_payload = payload.get("candidates")
    if not isinstance(candidates_payload, list):
        return False, "candidates must be a list"
    try:
        candidates = tuple(
            DecisionCandidate(
                candidate_index=candidate["candidate_index"],
                kind=DecisionCandidateKind(str(candidate["kind"])),
                requested=candidate["requested"],
                admissible=candidate["admissible"],
                candidate_key=candidate["candidate_key"],
            )
            for candidate in candidates_payload
        )
        candidate_set = StrategyCandidateSet(
            policy_artifact_hash=str(payload.get("policy_artifact_hash", "")),
            tau_policy_bundle_hash=str(payload.get("tau_policy_bundle_hash", "")),
            observation_hash=str(payload.get("observation_hash", "")),
            decision_model_version=str(payload.get("decision_model_version", "")),
            candidates=candidates,
        )
    except Exception as exc:
        return False, str(exc)
    if payload != candidate_set.to_dict():
        return False, "candidate set payload mismatch"
    return True, None


def verify_strategy_decision_certificate_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "decision certificate payload must be an object"
    if payload.get("schema") != DECISION_CERTIFICATE_SCHEMA:
        return False, "unsupported decision certificate schema"
    expected_hash = payload.get("decision_hash")
    unsigned_payload = {key: value for key, value in payload.items() if key != "decision_hash"}
    if expected_hash != sha256_hex(canonical_json_bytes(unsigned_payload)):
        return False, "decision_hash mismatch"
    argmax_steps = payload.get("argmax_steps")
    if not isinstance(argmax_steps, list):
        return False, "argmax_steps must be a list"
    winner_index = payload.get("winner_index")
    winner_key = payload.get("winner_key")
    kill_switch_active = payload.get("kill_switch_active")
    if not isinstance(winner_index, int) or isinstance(winner_index, bool):
        return False, "winner_index must be an int"
    if not isinstance(winner_key, int) or isinstance(winner_key, bool):
        return False, "winner_key must be an int"
    if not isinstance(kill_switch_active, bool):
        return False, "kill_switch_active must be a bool"
    try:
        certificate = StrategyDecisionCertificate(
            policy_artifact_hash=str(payload.get("policy_artifact_hash", "")),
            tau_policy_bundle_hash=str(payload.get("tau_policy_bundle_hash", "")),
            observation_hash=str(payload.get("observation_hash", "")),
            candidate_set_hash=str(payload.get("candidate_set_hash", "")),
            decision_model_version=str(payload.get("decision_model_version", "")),
            winner_index=winner_index,
            winner_kind=DecisionCandidateKind(str(payload.get("winner_kind", ""))),
            winner_key=winner_key,
            argmax_steps=tuple(dict(step) for step in argmax_steps),
            kill_switch_active=kill_switch_active,
        )
    except Exception as exc:
        return False, str(exc)
    if payload != certificate.to_dict():
        return False, "decision certificate payload mismatch"
    return True, None
