from __future__ import annotations

from dataclasses import dataclass
from typing import Any, TYPE_CHECKING, cast

from ..state.canonical import canonical_json_bytes, sha256_hex
from .autotrader_decision import observation_hash_hex

if TYPE_CHECKING:
    from .autotrader_live import AutoTraderLiveReport


STAGE_CERTIFICATE_SCHEMA = "zenodex/strategy-stage-certificate/v1"
_STAGES = (
    "signer",
    "tau_policy_bundle",
    "policy_artifact",
    "observation",
    "candidate_set",
    "decision",
    "live_release",
)


def _safe_payload_validation_error(exc: Exception) -> str:
    detail = " ".join(str(exc).split())
    return detail[:200] or type(exc).__name__


def _highest_stage(
    *,
    tau_policy_bundle_hash: str | None,
    policy_artifact_hash: str | None,
    observation_hash: str | None,
    candidate_set_hash: str | None,
    decision_hash: str | None,
) -> str:
    if (
        tau_policy_bundle_hash is not None
        and policy_artifact_hash is not None
        and observation_hash is not None
        and candidate_set_hash is not None
        and decision_hash is not None
    ):
        return "live_release"
    if decision_hash is not None:
        return "decision"
    if candidate_set_hash is not None:
        return "candidate_set"
    if observation_hash is not None:
        return "observation"
    if policy_artifact_hash is not None:
        return "policy_artifact"
    if tau_policy_bundle_hash is not None:
        return "tau_policy_bundle"
    return "signer"


def _derive_blocker(report: "AutoTraderLiveReport") -> str | None:
    for value in (
        report.live_release_certificate_error,
        report.emit_finalize_error,
        report.submit_bundle_error,
        report.live_admission_error,
        report.system_compose_error,
        report.decision_error,
        report.candidate_set_error,
        report.observation_packet_error,
        report.policy_artifact_error,
        report.tau_policy_bundle_error,
    ):
        if value:
            return value
    if report.decision.tag.value != "submit":
        return report.decision.reason
    return None


@dataclass(frozen=True)
class AutoTraderStageCertificate:
    signer_pubkey: str
    chain_id: str
    decision_tag: str
    tau_policy_bundle_hash: str | None
    policy_artifact_hash: str | None
    observation_hash: str | None
    candidate_set_hash: str | None
    decision_hash: str | None
    highest_stage: str
    release_eligible: bool
    blocker: str | None

    def __post_init__(self) -> None:
        for name in ("signer_pubkey", "chain_id", "decision_tag", "highest_stage"):
            value = getattr(self, name)
            if not isinstance(value, str) or not value.strip():
                raise ValueError(f"{name} must be a non-empty string")
        if self.highest_stage not in _STAGES:
            raise ValueError(f"unknown highest_stage: {self.highest_stage}")
        if not isinstance(self.release_eligible, bool):
            raise TypeError("release_eligible must be a bool")
        if self.blocker is not None and not isinstance(self.blocker, str):
            raise TypeError("blocker must be a string or None")
        for name in (
            "tau_policy_bundle_hash",
            "policy_artifact_hash",
            "observation_hash",
            "candidate_set_hash",
            "decision_hash",
        ):
            value = getattr(self, name)
            if value is not None and (not isinstance(value, str) or not value.strip()):
                raise ValueError(f"{name} must be a non-empty string when present")
        if self.release_eligible != (self.highest_stage == "live_release"):
            raise ValueError("release_eligible must agree with highest_stage")

    def to_unsigned_dict(self) -> dict[str, Any]:
        return {
            "schema": STAGE_CERTIFICATE_SCHEMA,
            "signer_pubkey": self.signer_pubkey,
            "chain_id": self.chain_id,
            "decision_tag": self.decision_tag,
            "tau_policy_bundle_hash": self.tau_policy_bundle_hash,
            "policy_artifact_hash": self.policy_artifact_hash,
            "observation_hash": self.observation_hash,
            "candidate_set_hash": self.candidate_set_hash,
            "decision_hash": self.decision_hash,
            "highest_stage": self.highest_stage,
            "release_eligible": bool(self.release_eligible),
            "blocker": self.blocker,
        }

    def to_dict(self) -> dict[str, Any]:
        payload = self.to_unsigned_dict()
        payload["stage_hash"] = self.stage_hash_hex()
        return payload

    def stage_hash_hex(self) -> str:
        return sha256_hex(canonical_json_bytes(self.to_unsigned_dict()))


def build_autotrader_stage_certificate(
    report: "AutoTraderLiveReport",
) -> AutoTraderStageCertificate:
    from .autotrader_live import AutoTraderLiveReport

    if not isinstance(report, AutoTraderLiveReport):
        raise TypeError("report must be an AutoTraderLiveReport")

    tau_policy_bundle_hash = (
        None
        if report.tau_policy_bundle is None
        else report.tau_policy_bundle.tau_policy_bundle_hash_hex()
    )
    policy_artifact_hash = (
        None
        if report.policy_artifact is None
        else report.policy_artifact.policy_artifact_hash_hex()
    )
    observation_hash = (
        None if report.observation_packet is None else observation_hash_hex(report.observation_packet)
    )
    candidate_set_hash = (
        None if report.candidate_set is None else report.candidate_set.candidate_set_hash_hex()
    )
    decision_hash = (
        None if report.decision_certificate is None else report.decision_certificate.decision_hash_hex()
    )
    highest_stage = _highest_stage(
        tau_policy_bundle_hash=tau_policy_bundle_hash,
        policy_artifact_hash=policy_artifact_hash,
        observation_hash=observation_hash,
        candidate_set_hash=candidate_set_hash,
        decision_hash=decision_hash,
    )
    return AutoTraderStageCertificate(
        signer_pubkey=report.signer_pubkey,
        chain_id=report.chain_id,
        decision_tag=report.decision.tag.value,
        tau_policy_bundle_hash=tau_policy_bundle_hash,
        policy_artifact_hash=policy_artifact_hash,
        observation_hash=observation_hash,
        candidate_set_hash=candidate_set_hash,
        decision_hash=decision_hash,
        highest_stage=highest_stage,
        release_eligible=(highest_stage == "live_release"),
        blocker=_derive_blocker(report),
    )


def verify_autotrader_stage_certificate(
    report: "AutoTraderLiveReport",
    certificate: AutoTraderStageCertificate,
) -> tuple[bool, str | None]:
    from .autotrader_live import AutoTraderLiveReport

    if not isinstance(report, AutoTraderLiveReport):
        raise TypeError("report must be an AutoTraderLiveReport")
    if not isinstance(certificate, AutoTraderStageCertificate):
        raise TypeError("certificate must be an AutoTraderStageCertificate")

    expected = build_autotrader_stage_certificate(report)
    for field_name in (
        "signer_pubkey",
        "chain_id",
        "decision_tag",
        "tau_policy_bundle_hash",
        "policy_artifact_hash",
        "observation_hash",
        "candidate_set_hash",
        "decision_hash",
        "highest_stage",
        "release_eligible",
        "blocker",
    ):
        if getattr(certificate, field_name) != getattr(expected, field_name):
            return False, f"{field_name} mismatch"
    return True, None


def verify_autotrader_stage_certificate_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "stage certificate payload must be an object"
    if payload.get("schema") != STAGE_CERTIFICATE_SCHEMA:
        return False, "unsupported stage certificate schema"
    expected_hash = payload.get("stage_hash")
    unsigned_payload = {key: value for key, value in payload.items() if key != "stage_hash"}
    if expected_hash != sha256_hex(canonical_json_bytes(unsigned_payload)):
        return False, "stage_hash mismatch"
    try:
        certificate = AutoTraderStageCertificate(
            signer_pubkey=str(payload.get("signer_pubkey", "")),
            chain_id=str(payload.get("chain_id", "")),
            decision_tag=str(payload.get("decision_tag", "")),
            tau_policy_bundle_hash=payload.get("tau_policy_bundle_hash"),
            policy_artifact_hash=payload.get("policy_artifact_hash"),
            observation_hash=payload.get("observation_hash"),
            candidate_set_hash=payload.get("candidate_set_hash"),
            decision_hash=payload.get("decision_hash"),
            highest_stage=str(payload.get("highest_stage", "")),
            release_eligible=cast(bool, payload.get("release_eligible")),
            blocker=payload.get("blocker"),
        )
    except (TypeError, ValueError) as exc:
        return False, _safe_payload_validation_error(exc)
    if payload != certificate.to_dict():
        return False, "stage certificate payload mismatch"
    return True, None
