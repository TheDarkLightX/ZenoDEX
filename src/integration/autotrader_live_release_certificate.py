from __future__ import annotations

from dataclasses import dataclass
from typing import Any, TYPE_CHECKING, cast

from .autotrader_controller import AutoTraderDecisionTag
from .autotrader_decision import observation_hash_hex
from ..state.canonical import canonical_json_bytes, sha256_hex

if TYPE_CHECKING:
    from .autotrader_live import AutoTraderLiveReport


LIVE_RELEASE_SCHEMA = "zenodex/strategy-live-release/v1"
def _derive_release_error(
    *,
    emit_requested: bool,
    live_admission_ok: bool,
    live_admission_error: str | None,
    system_compose_ok: bool,
    system_compose_error: str | None,
    submit_bundle_ok: bool,
    submit_bundle_error: str | None,
    emit_finalize_ok: bool,
    emit_finalize_error: str | None,
) -> str | None:
    if not live_admission_ok:
        return live_admission_error or "live_admission_rejected"
    if not system_compose_ok:
        return system_compose_error or "system_compose_rejected"
    if not submit_bundle_ok:
        return submit_bundle_error or "submit_bundle_rejected"
    if not emit_finalize_ok:
        return emit_finalize_error or "emit_finalize_rejected"
    if not emit_requested:
        return "emit_not_requested"
    return None


@dataclass(frozen=True)
class AutoTraderLiveReleaseCertificate:
    policy_artifact_hash: str
    tau_policy_bundle_hash: str
    observation_hash: str
    candidate_set_hash: str
    decision_hash: str
    decision_model_version: str
    emit_requested: bool
    live_admission_ok: bool
    system_compose_ok: bool
    submit_bundle_ok: bool
    emit_finalize_ok: bool
    release_ok: bool
    release_error: str | None = None

    def __post_init__(self) -> None:
        for name in (
            "policy_artifact_hash",
            "tau_policy_bundle_hash",
            "observation_hash",
            "candidate_set_hash",
            "decision_hash",
            "decision_model_version",
        ):
            value = getattr(self, name)
            if not isinstance(value, str) or not value.strip():
                raise ValueError(f"{name} must be a non-empty string")
        for name in (
            "emit_requested",
            "live_admission_ok",
            "system_compose_ok",
            "submit_bundle_ok",
            "emit_finalize_ok",
            "release_ok",
        ):
            value = getattr(self, name)
            if not isinstance(value, bool):
                raise TypeError(f"{name} must be a bool")
        if self.release_error is not None and not isinstance(self.release_error, str):
            raise TypeError("release_error must be a string or None")

    def to_unsigned_dict(self) -> dict[str, Any]:
        return {
            "schema": LIVE_RELEASE_SCHEMA,
            "policy_artifact_hash": self.policy_artifact_hash,
            "tau_policy_bundle_hash": self.tau_policy_bundle_hash,
            "observation_hash": self.observation_hash,
            "candidate_set_hash": self.candidate_set_hash,
            "decision_hash": self.decision_hash,
            "decision_model_version": self.decision_model_version,
            "emit_requested": bool(self.emit_requested),
            "live_admission_ok": bool(self.live_admission_ok),
            "system_compose_ok": bool(self.system_compose_ok),
            "submit_bundle_ok": bool(self.submit_bundle_ok),
            "emit_finalize_ok": bool(self.emit_finalize_ok),
            "release_ok": bool(self.release_ok),
            "release_error": self.release_error,
        }

    def to_dict(self) -> dict[str, Any]:
        payload = self.to_unsigned_dict()
        payload["release_hash"] = self.release_hash_hex()
        return payload

    def release_hash_hex(self) -> str:
        return sha256_hex(canonical_json_bytes(self.to_unsigned_dict()))


def build_autotrader_live_release_certificate(
    report: "AutoTraderLiveReport",
) -> AutoTraderLiveReleaseCertificate:
    from .autotrader_live import AutoTraderLiveReport

    if not isinstance(report, AutoTraderLiveReport):
        raise TypeError("report must be an AutoTraderLiveReport")
    if report.policy_artifact is None:
        raise ValueError("report.policy_artifact is required")
    if report.tau_policy_bundle is None:
        raise ValueError("report.tau_policy_bundle is required")
    if report.observation_packet is None:
        raise ValueError("report.observation_packet is required")
    if report.candidate_set is None:
        raise ValueError("report.candidate_set is required")
    if report.decision_certificate is None:
        raise ValueError("report.decision_certificate is required")

    emit_requested = report.decision.tag is AutoTraderDecisionTag.SUBMIT
    live_admission_ok = bool(report.live_admission_ok)
    system_compose_ok = bool(report.system_compose_ok)
    submit_bundle_ok = bool(report.submit_bundle_ok)
    emit_finalize_ok = bool(report.emit_finalize_ok)
    release_ok = (
        emit_requested
        and live_admission_ok
        and system_compose_ok
        and submit_bundle_ok
        and emit_finalize_ok
    )
    release_error = _derive_release_error(
        emit_requested=emit_requested,
        live_admission_ok=live_admission_ok,
        live_admission_error=report.live_admission_error,
        system_compose_ok=system_compose_ok,
        system_compose_error=report.system_compose_error,
        submit_bundle_ok=submit_bundle_ok,
        submit_bundle_error=report.submit_bundle_error,
        emit_finalize_ok=emit_finalize_ok,
        emit_finalize_error=report.emit_finalize_error,
    )
    return AutoTraderLiveReleaseCertificate(
        policy_artifact_hash=report.policy_artifact.policy_artifact_hash_hex(),
        tau_policy_bundle_hash=report.tau_policy_bundle.tau_policy_bundle_hash_hex(),
        observation_hash=observation_hash_hex(report.observation_packet),
        candidate_set_hash=report.candidate_set.candidate_set_hash_hex(),
        decision_hash=report.decision_certificate.decision_hash_hex(),
        decision_model_version=report.decision_certificate.decision_model_version,
        emit_requested=emit_requested,
        live_admission_ok=live_admission_ok,
        system_compose_ok=system_compose_ok,
        submit_bundle_ok=submit_bundle_ok,
        emit_finalize_ok=emit_finalize_ok,
        release_ok=release_ok,
        release_error=release_error,
    )


def verify_autotrader_live_release_certificate(
    report: "AutoTraderLiveReport",
    certificate: AutoTraderLiveReleaseCertificate,
) -> tuple[bool, str | None]:
    from .autotrader_live import AutoTraderLiveReport

    if not isinstance(report, AutoTraderLiveReport):
        raise TypeError("report must be an AutoTraderLiveReport")
    if not isinstance(certificate, AutoTraderLiveReleaseCertificate):
        raise TypeError("certificate must be an AutoTraderLiveReleaseCertificate")

    expected = build_autotrader_live_release_certificate(report)
    for field_name in (
        "policy_artifact_hash",
        "tau_policy_bundle_hash",
        "observation_hash",
        "candidate_set_hash",
        "decision_hash",
        "decision_model_version",
        "emit_requested",
        "live_admission_ok",
        "system_compose_ok",
        "submit_bundle_ok",
        "emit_finalize_ok",
        "release_ok",
        "release_error",
    ):
        if getattr(certificate, field_name) != getattr(expected, field_name):
            return False, f"{field_name} mismatch"
    return True, None


def verify_autotrader_live_release_certificate_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "live release certificate payload must be an object"
    if payload.get("schema") != LIVE_RELEASE_SCHEMA:
        return False, "unsupported live release certificate schema"
    expected_hash = payload.get("release_hash")
    unsigned_payload = {key: value for key, value in payload.items() if key != "release_hash"}
    if expected_hash != sha256_hex(canonical_json_bytes(unsigned_payload)):
        return False, "release_hash mismatch"
    try:
        certificate = AutoTraderLiveReleaseCertificate(
            policy_artifact_hash=str(payload.get("policy_artifact_hash", "")),
            tau_policy_bundle_hash=str(payload.get("tau_policy_bundle_hash", "")),
            observation_hash=str(payload.get("observation_hash", "")),
            candidate_set_hash=str(payload.get("candidate_set_hash", "")),
            decision_hash=str(payload.get("decision_hash", "")),
            decision_model_version=str(payload.get("decision_model_version", "")),
            emit_requested=cast(bool, payload.get("emit_requested")),
            live_admission_ok=cast(bool, payload.get("live_admission_ok")),
            system_compose_ok=cast(bool, payload.get("system_compose_ok")),
            submit_bundle_ok=cast(bool, payload.get("submit_bundle_ok")),
            emit_finalize_ok=cast(bool, payload.get("emit_finalize_ok")),
            release_ok=cast(bool, payload.get("release_ok")),
            release_error=payload.get("release_error"),
        )
    except (TypeError, ValueError) as exc:
        return False, str(exc)
    if payload != certificate.to_dict():
        return False, "live release certificate payload mismatch"
    return True, None
