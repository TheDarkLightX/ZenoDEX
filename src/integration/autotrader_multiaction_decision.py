from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any, Mapping

from ..agents.policy_artifacts import StrategyPolicyArtifact, TauPolicyBundle
from ..agents.strategy_ir import StrategyAction
from ..state.canonical import canonical_json_bytes, sha256_hex
from .autotrader_decision import observation_hash_hex
from .autotrader_signals import AutoTraderObservationPacket
from .tau_runner import run_tau_spec_steps
from .tau_witness import ARGMAX_STREAM_CERTIFICATE_V1, build_argmax_stream_certificate_v1_step

MULTI_ACTION_CANDIDATE_SET_SCHEMA = "zenodex/strategy-multi-action-candidate-set/v1"
MULTI_ACTION_DECISION_CERTIFICATE_SCHEMA = "zenodex/strategy-multi-action-decision/v1"
DEFAULT_MULTI_ACTION_MODEL_VERSION = "autotrader-multi-action-v1"


def _safe_payload_validation_error(exc: Exception) -> str:
    detail = " ".join(str(exc).split())
    return detail[:200] or type(exc).__name__


class MultiActionCandidateKind(Enum):
    NO_OP = "no_op"
    PLACE_ORDER_INTENT = StrategyAction.PLACE_ORDER_INTENT.value
    PLACE_SWAP_EXACT_IN = StrategyAction.PLACE_SWAP_EXACT_IN.value
    PLACE_SWAP_EXACT_OUT = StrategyAction.PLACE_SWAP_EXACT_OUT.value

    @classmethod
    def from_strategy_action(cls, action: StrategyAction) -> "MultiActionCandidateKind":
        if not isinstance(action, StrategyAction):
            raise TypeError("action must be a StrategyAction")
        return cls(action.value)


def derive_multi_action_candidate_key(
    *,
    requested: bool,
    admissible: bool,
    action_priority: int,
) -> int:
    if not isinstance(requested, bool):
        raise TypeError("requested must be a bool")
    if not isinstance(admissible, bool):
        raise TypeError("admissible must be a bool")
    if not isinstance(action_priority, int) or isinstance(action_priority, bool):
        raise TypeError("action_priority must be an int")
    if action_priority < 0 or action_priority > 0xFFFFFFFF:
        raise ValueError(f"action_priority out of range: {action_priority}")
    return (
        (int(admissible) << 48)
        | (int(requested) << 32)
        | int(action_priority)
    )


@dataclass(frozen=True)
class MultiActionDecisionCandidate:
    candidate_index: int
    kind: MultiActionCandidateKind
    requested: bool
    admissible: bool
    action_priority: int
    candidate_key: int

    def __post_init__(self) -> None:
        if not isinstance(self.candidate_index, int) or isinstance(self.candidate_index, bool):
            raise TypeError("candidate_index must be an int")
        if self.candidate_index < 0 or self.candidate_index > 0xFFFFFFFF:
            raise ValueError(f"candidate_index out of range: {self.candidate_index}")
        if not isinstance(self.kind, MultiActionCandidateKind):
            raise TypeError("kind must be a MultiActionCandidateKind")
        if not isinstance(self.requested, bool):
            raise TypeError("requested must be a bool")
        if not isinstance(self.admissible, bool):
            raise TypeError("admissible must be a bool")
        if not isinstance(self.action_priority, int) or isinstance(self.action_priority, bool):
            raise TypeError("action_priority must be an int")
        if self.action_priority < 0 or self.action_priority > 0xFFFFFFFF:
            raise ValueError(f"action_priority out of range: {self.action_priority}")
        if not isinstance(self.candidate_key, int) or isinstance(self.candidate_key, bool):
            raise TypeError("candidate_key must be an int")
        if self.candidate_key < 0 or self.candidate_key > 0xFFFFFFFFFFFFFFFF:
            raise ValueError(f"candidate_key out of range: {self.candidate_key}")
        expected_key = derive_multi_action_candidate_key(
            requested=self.requested,
            admissible=self.admissible,
            action_priority=self.action_priority,
        )
        if self.candidate_key != expected_key:
            raise ValueError("candidate_key must equal the derived multi-action key")
        if self.kind is MultiActionCandidateKind.NO_OP:
            if self.candidate_index != 0:
                raise ValueError("NO_OP candidate must have index 0")
            if not self.requested or not self.admissible:
                raise ValueError("NO_OP candidate must be requested and admissible")
            if self.action_priority != 0:
                raise ValueError("NO_OP candidate must have action_priority = 0")

    def to_dict(self) -> dict[str, Any]:
        return {
            "candidate_index": int(self.candidate_index),
            "kind": self.kind.value,
            "requested": bool(self.requested),
            "admissible": bool(self.admissible),
            "action_priority": int(self.action_priority),
            "candidate_key": int(self.candidate_key),
        }


@dataclass(frozen=True)
class BoundedMultiActionCandidateSet:
    policy_artifact_hash: str
    tau_policy_bundle_hash: str
    observation_hash: str
    decision_model_version: str
    candidates: tuple[MultiActionDecisionCandidate, ...]

    def __post_init__(self) -> None:
        for name in (
            "policy_artifact_hash",
            "tau_policy_bundle_hash",
            "observation_hash",
            "decision_model_version",
        ):
            value = getattr(self, name)
            if not isinstance(value, str) or not value.strip():
                raise ValueError(f"{name} must be a non-empty string")
        if len(self.candidates) < 2:
            raise ValueError("bounded multi-action candidate set must contain at least two candidates")
        seen_indices: set[int] = set()
        seen_kinds: set[MultiActionCandidateKind] = set()
        for expected_index, candidate in enumerate(self.candidates):
            if candidate.candidate_index != expected_index:
                raise ValueError("candidate indices must be contiguous from 0")
            if candidate.candidate_index in seen_indices:
                raise ValueError(f"duplicate candidate_index: {candidate.candidate_index}")
            if candidate.kind in seen_kinds:
                raise ValueError(f"duplicate candidate kind: {candidate.kind.value}")
            seen_indices.add(candidate.candidate_index)
            seen_kinds.add(candidate.kind)
        if self.candidates[0].kind is not MultiActionCandidateKind.NO_OP:
            raise ValueError("candidate 0 must be NO_OP")

    def to_unsigned_dict(self) -> dict[str, Any]:
        return {
            "schema": MULTI_ACTION_CANDIDATE_SET_SCHEMA,
            "policy_artifact_hash": self.policy_artifact_hash,
            "tau_policy_bundle_hash": self.tau_policy_bundle_hash,
            "observation_hash": self.observation_hash,
            "decision_model_version": self.decision_model_version,
            "candidate_count": len(self.candidates),
            "candidates": [candidate.to_dict() for candidate in self.candidates],
        }

    def to_dict(self) -> dict[str, Any]:
        payload = self.to_unsigned_dict()
        payload["candidate_set_hash"] = self.candidate_set_hash_hex()
        return payload

    def candidate_set_hash_hex(self) -> str:
        return sha256_hex(canonical_json_bytes(self.to_unsigned_dict()))


@dataclass(frozen=True)
class BoundedMultiActionDecisionCertificate:
    policy_artifact_hash: str
    tau_policy_bundle_hash: str
    observation_hash: str
    candidate_set_hash: str
    decision_model_version: str
    winner_index: int
    winner_kind: MultiActionCandidateKind
    winner_key: int
    frontier_width: int
    argmax_steps: tuple[dict[str, int], ...]

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
        if self.winner_index < 0 or self.winner_index > 0xFFFFFFFF:
            raise ValueError(f"winner_index out of range: {self.winner_index}")
        if not isinstance(self.winner_kind, MultiActionCandidateKind):
            raise TypeError("winner_kind must be a MultiActionCandidateKind")
        if not isinstance(self.winner_key, int) or isinstance(self.winner_key, bool):
            raise TypeError("winner_key must be an int")
        if self.winner_key < 0 or self.winner_key > 0xFFFFFFFFFFFFFFFF:
            raise ValueError(f"winner_key out of range: {self.winner_key}")
        if not isinstance(self.frontier_width, int) or isinstance(self.frontier_width, bool):
            raise TypeError("frontier_width must be an int")
        if self.frontier_width < 2 or self.frontier_width > 0xFFFFFFFF:
            raise ValueError(f"frontier_width out of range: {self.frontier_width}")
        if not self.argmax_steps:
            raise ValueError("argmax_steps must be non-empty")

    def to_unsigned_dict(self) -> dict[str, Any]:
        return {
            "schema": MULTI_ACTION_DECISION_CERTIFICATE_SCHEMA,
            "policy_artifact_hash": self.policy_artifact_hash,
            "tau_policy_bundle_hash": self.tau_policy_bundle_hash,
            "observation_hash": self.observation_hash,
            "candidate_set_hash": self.candidate_set_hash,
            "decision_model_version": self.decision_model_version,
            "winner_index": int(self.winner_index),
            "winner_kind": self.winner_kind.value,
            "winner_key": int(self.winner_key),
            "frontier_width": int(self.frontier_width),
            "argmax_steps": [dict(step) for step in self.argmax_steps],
        }

    def to_dict(self) -> dict[str, Any]:
        payload = self.to_unsigned_dict()
        payload["decision_hash"] = self.decision_hash_hex()
        return payload

    def decision_hash_hex(self) -> str:
        return sha256_hex(canonical_json_bytes(self.to_unsigned_dict()))


@dataclass(frozen=True)
class BoundedMultiActionTauArgmaxContractResult:
    ok: bool | None
    certificate_ok: bool
    binding_ok: bool
    frontier_width_ok: bool
    argmax_steps_ok: bool | None
    tau_enabled: bool
    tau_used: bool
    step_count: int
    error: str | None = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "ok": self.ok,
            "certificate_ok": bool(self.certificate_ok),
            "binding_ok": bool(self.binding_ok),
            "frontier_width_ok": bool(self.frontier_width_ok),
            "argmax_steps_ok": self.argmax_steps_ok,
            "tau_enabled": bool(self.tau_enabled),
            "tau_used": bool(self.tau_used),
            "tau_spec_id": ARGMAX_STREAM_CERTIFICATE_V1.spec_id,
            "step_count": int(self.step_count),
            "error": self.error,
        }


def _winner_for_candidates(
    candidates: tuple[MultiActionDecisionCandidate, ...],
) -> MultiActionDecisionCandidate:
    return max(candidates, key=lambda candidate: (candidate.candidate_key, -candidate.candidate_index))


def build_bounded_multi_action_candidate_set(
    *,
    policy_artifact: StrategyPolicyArtifact,
    tau_policy_bundle: TauPolicyBundle,
    observation_packet: AutoTraderObservationPacket,
    action_frontier: Mapping[StrategyAction, tuple[bool, bool, int]],
    decision_model_version: str = DEFAULT_MULTI_ACTION_MODEL_VERSION,
) -> BoundedMultiActionCandidateSet:
    if not isinstance(policy_artifact, StrategyPolicyArtifact):
        raise TypeError("policy_artifact must be a StrategyPolicyArtifact")
    if not isinstance(tau_policy_bundle, TauPolicyBundle):
        raise TypeError("tau_policy_bundle must be a TauPolicyBundle")
    if not isinstance(action_frontier, Mapping):
        raise TypeError("action_frontier must be a mapping")
    if not isinstance(decision_model_version, str) or not decision_model_version.strip():
        raise ValueError("decision_model_version must be a non-empty string")
    frontier_items = list(action_frontier.items())
    for action, _ in frontier_items:
        if not isinstance(action, StrategyAction):
            raise TypeError("action_frontier keys must be StrategyAction members")
    ordered_actions = sorted(frontier_items, key=lambda item: item[0].value)
    if not ordered_actions:
        raise ValueError("action_frontier must be non-empty")

    candidates: list[MultiActionDecisionCandidate] = [
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
        )
    ]
    for index, (action, frontier) in enumerate(ordered_actions, start=1):
        if (
            not isinstance(frontier, tuple)
            or len(frontier) != 3
        ):
            raise TypeError("action_frontier values must be (requested, admissible, action_priority) tuples")
        requested, admissible, action_priority = frontier
        kind = MultiActionCandidateKind.from_strategy_action(action)
        candidate_key = derive_multi_action_candidate_key(
            requested=requested,
            admissible=admissible,
            action_priority=action_priority,
        )
        candidates.append(
            MultiActionDecisionCandidate(
                candidate_index=index,
                kind=kind,
                requested=requested,
                admissible=admissible,
                action_priority=action_priority,
                candidate_key=candidate_key,
            )
        )

    return BoundedMultiActionCandidateSet(
        policy_artifact_hash=policy_artifact.policy_artifact_hash_hex(),
        tau_policy_bundle_hash=tau_policy_bundle.tau_policy_bundle_hash_hex(),
        observation_hash=observation_hash_hex(observation_packet),
        decision_model_version=decision_model_version.strip(),
        candidates=tuple(candidates),
    )


def derive_bounded_multi_action_decision_binding_ok(
    *,
    candidate_set: BoundedMultiActionCandidateSet,
    winner_index: int,
    winner_key: int,
) -> bool:
    if not isinstance(candidate_set, BoundedMultiActionCandidateSet):
        raise TypeError("candidate_set must be a BoundedMultiActionCandidateSet")
    if not isinstance(winner_index, int) or isinstance(winner_index, bool):
        raise TypeError("winner_index must be an int")
    if not isinstance(winner_key, int) or isinstance(winner_key, bool):
        raise TypeError("winner_key must be an int")
    expected = _winner_for_candidates(candidate_set.candidates)
    return (
        winner_index == expected.candidate_index
        and winner_key == expected.candidate_key
        and candidate_set.candidate_set_hash_hex()
        == sha256_hex(canonical_json_bytes(candidate_set.to_unsigned_dict()))
    )


def build_bounded_multi_action_decision_certificate(
    *,
    candidate_set: BoundedMultiActionCandidateSet,
) -> BoundedMultiActionDecisionCertificate:
    if not isinstance(candidate_set, BoundedMultiActionCandidateSet):
        raise TypeError("candidate_set must be a BoundedMultiActionCandidateSet")
    winner = _winner_for_candidates(candidate_set.candidates)
    binding_ok = int(
        derive_bounded_multi_action_decision_binding_ok(
            candidate_set=candidate_set,
            winner_index=winner.candidate_index,
            winner_key=winner.candidate_key,
        )
    )
    argmax_steps = tuple(
        build_argmax_stream_certificate_v1_step(
            winner_key=winner.candidate_key,
            winner_index=winner.candidate_index,
            cand_key=candidate.candidate_key,
            cand_index=candidate.candidate_index,
            binding_ok=binding_ok,
        )
        for candidate in candidate_set.candidates
    )
    return BoundedMultiActionDecisionCertificate(
        policy_artifact_hash=candidate_set.policy_artifact_hash,
        tau_policy_bundle_hash=candidate_set.tau_policy_bundle_hash,
        observation_hash=candidate_set.observation_hash,
        candidate_set_hash=candidate_set.candidate_set_hash_hex(),
        decision_model_version=candidate_set.decision_model_version,
        winner_index=winner.candidate_index,
        winner_kind=winner.kind,
        winner_key=winner.candidate_key,
        frontier_width=len(candidate_set.candidates),
        argmax_steps=argmax_steps,
    )


def verify_bounded_multi_action_decision_certificate(
    *,
    candidate_set: BoundedMultiActionCandidateSet,
    certificate: BoundedMultiActionDecisionCertificate,
) -> tuple[bool, str | None]:
    if not isinstance(candidate_set, BoundedMultiActionCandidateSet):
        raise TypeError("candidate_set must be a BoundedMultiActionCandidateSet")
    if not isinstance(certificate, BoundedMultiActionDecisionCertificate):
        raise TypeError("certificate must be a BoundedMultiActionDecisionCertificate")
    expected = build_bounded_multi_action_decision_certificate(candidate_set=candidate_set)
    for field_name in (
        "policy_artifact_hash",
        "tau_policy_bundle_hash",
        "observation_hash",
        "candidate_set_hash",
        "decision_model_version",
        "winner_index",
        "winner_kind",
        "winner_key",
        "frontier_width",
        "argmax_steps",
    ):
        if getattr(certificate, field_name) != getattr(expected, field_name):
            return False, f"{field_name} mismatch"
    return True, None


def check_bounded_multi_action_decision_tau_argmax_contract(
    *,
    candidate_set: BoundedMultiActionCandidateSet,
    certificate: BoundedMultiActionDecisionCertificate,
    tau_bin: str | None,
    timeout_s: float = 2.0,
) -> BoundedMultiActionTauArgmaxContractResult:
    certificate_ok, certificate_error = verify_bounded_multi_action_decision_certificate(
        candidate_set=candidate_set,
        certificate=certificate,
    )
    binding_ok = derive_bounded_multi_action_decision_binding_ok(
        candidate_set=candidate_set,
        winner_index=certificate.winner_index,
        winner_key=certificate.winner_key,
    )
    frontier_width_ok = (
        certificate.frontier_width == len(candidate_set.candidates)
        and certificate.frontier_width >= 2
    )
    if not tau_bin:
        return BoundedMultiActionTauArgmaxContractResult(
            ok=None,
            certificate_ok=bool(certificate_ok),
            binding_ok=bool(binding_ok),
            frontier_width_ok=bool(frontier_width_ok),
            argmax_steps_ok=None,
            tau_enabled=False,
            tau_used=False,
            step_count=len(certificate.argmax_steps),
            error="tau_disabled",
        )
    if not certificate_ok:
        return BoundedMultiActionTauArgmaxContractResult(
            ok=False,
            certificate_ok=False,
            binding_ok=bool(binding_ok),
            frontier_width_ok=bool(frontier_width_ok),
            argmax_steps_ok=None,
            tau_enabled=True,
            tau_used=False,
            step_count=len(certificate.argmax_steps),
            error=certificate_error or "certificate_mismatch",
        )
    try:
        outputs = run_tau_spec_steps(
            tau_bin=tau_bin,
            spec_path=ARGMAX_STREAM_CERTIFICATE_V1.path,
            steps=[dict(step) for step in certificate.argmax_steps],
            timeout_s=timeout_s,
        )
    except Exception as exc:
        return BoundedMultiActionTauArgmaxContractResult(
            ok=False,
            certificate_ok=True,
            binding_ok=bool(binding_ok),
            frontier_width_ok=bool(frontier_width_ok),
            argmax_steps_ok=False,
            tau_enabled=True,
            tau_used=True,
            step_count=len(certificate.argmax_steps),
            error=f"{type(exc).__name__}:{exc}",
        )
    argmax_steps_ok = (
        len(outputs) == len(certificate.argmax_steps)
        and all(outputs[idx].get(ARGMAX_STREAM_CERTIFICATE_V1.gate_output) == 1 for idx in range(len(certificate.argmax_steps)))
    )
    ok = bool(certificate_ok and binding_ok and frontier_width_ok and argmax_steps_ok)
    if not binding_ok:
        error = "binding_mismatch"
    elif not frontier_width_ok:
        error = "frontier_width_mismatch"
    elif not argmax_steps_ok:
        error = "tau_argmax_rejected"
    else:
        error = None
    return BoundedMultiActionTauArgmaxContractResult(
        ok=ok,
        certificate_ok=True,
        binding_ok=bool(binding_ok),
        frontier_width_ok=bool(frontier_width_ok),
        argmax_steps_ok=bool(argmax_steps_ok),
        tau_enabled=True,
        tau_used=True,
        step_count=len(certificate.argmax_steps),
        error=error,
    )


def verify_bounded_multi_action_candidate_set_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "bounded multi-action candidate set payload must be an object"
    if payload.get("schema") != MULTI_ACTION_CANDIDATE_SET_SCHEMA:
        return False, "unsupported bounded multi-action candidate set schema"
    expected_hash = payload.get("candidate_set_hash")
    unsigned_payload = {key: value for key, value in payload.items() if key != "candidate_set_hash"}
    if expected_hash != sha256_hex(canonical_json_bytes(unsigned_payload)):
        return False, "candidate_set_hash mismatch"
    candidates_payload = payload.get("candidates")
    if not isinstance(candidates_payload, list):
        return False, "candidates must be a list"
    try:
        candidates = tuple(
            MultiActionDecisionCandidate(
                candidate_index=candidate["candidate_index"],
                kind=MultiActionCandidateKind(str(candidate["kind"])),
                requested=candidate["requested"],
                admissible=candidate["admissible"],
                action_priority=candidate["action_priority"],
                candidate_key=candidate["candidate_key"],
            )
            for candidate in candidates_payload
        )
        candidate_set = BoundedMultiActionCandidateSet(
            policy_artifact_hash=str(payload.get("policy_artifact_hash", "")),
            tau_policy_bundle_hash=str(payload.get("tau_policy_bundle_hash", "")),
            observation_hash=str(payload.get("observation_hash", "")),
            decision_model_version=str(payload.get("decision_model_version", "")),
            candidates=candidates,
        )
    except Exception as exc:
        return False, _safe_payload_validation_error(exc)
    if payload != candidate_set.to_dict():
        return False, "bounded multi-action candidate set payload mismatch"
    return True, None


def verify_bounded_multi_action_decision_certificate_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "bounded multi-action decision certificate payload must be an object"
    if payload.get("schema") != MULTI_ACTION_DECISION_CERTIFICATE_SCHEMA:
        return False, "unsupported bounded multi-action decision certificate schema"
    expected_hash = payload.get("decision_hash")
    unsigned_payload = {key: value for key, value in payload.items() if key != "decision_hash"}
    if expected_hash != sha256_hex(canonical_json_bytes(unsigned_payload)):
        return False, "decision_hash mismatch"
    argmax_steps = payload.get("argmax_steps")
    if not isinstance(argmax_steps, list):
        return False, "argmax_steps must be a list"
    winner_index = payload.get("winner_index")
    winner_key = payload.get("winner_key")
    frontier_width = payload.get("frontier_width")
    if not isinstance(winner_index, int) or isinstance(winner_index, bool):
        return False, "winner_index must be an int"
    if not isinstance(winner_key, int) or isinstance(winner_key, bool):
        return False, "winner_key must be an int"
    if not isinstance(frontier_width, int) or isinstance(frontier_width, bool):
        return False, "frontier_width must be an int"
    try:
        certificate = BoundedMultiActionDecisionCertificate(
            policy_artifact_hash=str(payload.get("policy_artifact_hash", "")),
            tau_policy_bundle_hash=str(payload.get("tau_policy_bundle_hash", "")),
            observation_hash=str(payload.get("observation_hash", "")),
            candidate_set_hash=str(payload.get("candidate_set_hash", "")),
            decision_model_version=str(payload.get("decision_model_version", "")),
            winner_index=winner_index,
            winner_kind=MultiActionCandidateKind(str(payload.get("winner_kind", ""))),
            winner_key=winner_key,
            frontier_width=frontier_width,
            argmax_steps=tuple(dict(step) for step in argmax_steps),
        )
    except Exception as exc:
        return False, _safe_payload_validation_error(exc)
    if payload != certificate.to_dict():
        return False, "bounded multi-action decision certificate payload mismatch"
    return True, None
