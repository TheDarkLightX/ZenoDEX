"""Typed ZenoOracle authorization checks for critical runtime consumers."""

from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass
from typing import Any, Mapping


SCHEMA = "zenodex/oracle-authorization-semantic-binding-check/v1"
EVIDENCE_RANK = {"O0": 0, "O1": 1, "O2": 2, "O3": 3, "O4": 4, "O5": 5}

CRITICAL_CONSUMER_PROFILES: dict[tuple[str, str], str] = {
    ("zenodex.zusd", "bootstrap_oracle"): "critical-zusd-v1",
    ("zenodex.zusd", "oracle_report"): "critical-zusd-v1",
    ("zenodex.zusd", "oracle_commit"): "critical-zusd-v1",
    ("zenodex.zusd", "mint"): "critical-zusd-v1",
    ("zenodex.zusd", "liquidate"): "critical-zusd-v1",
    ("zenodex.perps", "settle_epoch"): "critical-perps-v1",
    ("zenodex.perps", "liquidate"): "critical-perps-v1",
    ("zenodex.routing", "protected_swap"): "critical-routing-v1",
    ("zenodex.trigger", "execute"): "critical-trigger-v1",
    ("zenodex.settlement", "critical_settlement"): "critical-settlement-v1",
}


@dataclass(frozen=True)
class OracleAuthorization:
    consumer_module: str
    action_kind: str
    action_id: str
    action_facts_hash: str
    pre_state_hash: str
    profile_id: str
    query_id: str
    value_e8: int
    value_hash: str
    confidence_e8: int
    deviation_bps: int
    observed_epoch: int
    expires_at_epoch: int
    feed_id: str
    feed_registry_root: str
    query_policy_root: str
    source_registry_root: str
    reporter_registry_root: str
    evidence_class: str
    economic_envelope_id: str
    receipt_graph_root: str


@dataclass(frozen=True)
class RuntimeActionFacts:
    consumer_module: str
    action_kind: str
    action_id: str
    action_facts_hash: str
    pre_state_hash: str
    profile_id: str
    query_id: str
    runtime_value_e8: int
    now_epoch: int


def _canonical_bytes(payload: Mapping[str, Any]) -> bytes:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def semantic_hash(domain: str, payload: Mapping[str, Any]) -> str:
    digest = hashlib.sha256(domain.encode("utf-8") + b"\x00" + _canonical_bytes(payload)).hexdigest()
    return f"sha256:{digest}"


def oracle_value_hash(*, query_id: str, value_e8: int, observed_epoch: int) -> str:
    return semantic_hash(
        "zenodex.oracle.value.v1",
        {
            "observed_epoch": int(observed_epoch),
            "query_id": str(query_id),
            "value_e8": int(value_e8),
        },
    )


def _is_sha256_ref(value: str) -> bool:
    if not isinstance(value, str) or not value.startswith("sha256:") or len(value) != 71:
        return False
    try:
        int(value.removeprefix("sha256:"), 16)
    except ValueError:
        return False
    return True


def verify_opaque_authorization(
    authorization: OracleAuthorization,
    runtime: RuntimeActionFacts,
) -> tuple[bool, tuple[str, ...]]:
    """Legacy comparison model: match opaque identifiers but not typed semantics."""

    errors: list[str] = []
    if authorization.consumer_module != runtime.consumer_module:
        errors.append("consumer_module mismatch")
    if authorization.action_kind != runtime.action_kind:
        errors.append("action_kind mismatch")
    if authorization.action_id != runtime.action_id:
        errors.append("action_id mismatch")
    if authorization.profile_id != runtime.profile_id:
        errors.append("profile_id mismatch")
    if authorization.query_id != runtime.query_id:
        errors.append("query_id mismatch")
    if runtime.now_epoch > authorization.expires_at_epoch:
        errors.append("authorization expired")
    return not errors, tuple(errors)


def verify_typed_authorization(
    authorization: OracleAuthorization,
    runtime: RuntimeActionFacts,
) -> tuple[bool, tuple[str, ...]]:
    """Typed comparison required for critical Oracle consumers."""

    ok, opaque_errors = verify_opaque_authorization(authorization, runtime)
    errors = list(opaque_errors)
    if int(runtime.now_epoch) < 0:
        errors.append("runtime now_epoch must be non-negative")
    if int(authorization.observed_epoch) < 0:
        errors.append("observed_epoch must be non-negative")
    if int(authorization.expires_at_epoch) < 0:
        errors.append("expires_at_epoch must be non-negative")
    if int(authorization.observed_epoch) > int(authorization.expires_at_epoch):
        errors.append("observed_epoch after expires_at_epoch")
    if int(authorization.observed_epoch) > int(runtime.now_epoch):
        errors.append("authorization observed in the future")
    if int(authorization.confidence_e8) < 0:
        errors.append("confidence_e8 must be non-negative")
    if int(authorization.deviation_bps) < 0 or int(authorization.deviation_bps) > 10_000:
        errors.append("deviation_bps must be in [0, 10000]")
    evidence_rank = EVIDENCE_RANK.get(authorization.evidence_class)
    if evidence_rank is None:
        errors.append("evidence_class must be one of O0..O5")
    elif evidence_rank < EVIDENCE_RANK["O3"]:
        errors.append("evidence_class below required O3")
    if authorization.action_facts_hash != runtime.action_facts_hash:
        errors.append("action_facts_hash mismatch")
    if authorization.pre_state_hash != runtime.pre_state_hash:
        errors.append("pre_state_hash mismatch")
    if int(authorization.value_e8) != int(runtime.runtime_value_e8):
        errors.append("runtime_value_e8 mismatch")
    expected_value_hash = oracle_value_hash(
        query_id=authorization.query_id,
        value_e8=authorization.value_e8,
        observed_epoch=authorization.observed_epoch,
    )
    if authorization.value_hash != expected_value_hash:
        errors.append("value_hash does not bind query_id/value_e8/observed_epoch")
    for key, value in (
        ("action_id", authorization.action_id),
        ("action_facts_hash", authorization.action_facts_hash),
        ("value_hash", authorization.value_hash),
        ("feed_registry_root", authorization.feed_registry_root),
        ("query_policy_root", authorization.query_policy_root),
        ("source_registry_root", authorization.source_registry_root),
        ("reporter_registry_root", authorization.reporter_registry_root),
        ("receipt_graph_root", authorization.receipt_graph_root),
    ):
        if not _is_sha256_ref(value):
            errors.append(f"{key} must be a sha256 reference")
    return bool(ok and not errors), tuple(errors)


def _require_str(obj: Mapping[str, Any], key: str) -> str:
    value = obj.get(key)
    if not isinstance(value, str) or not value:
        raise ValueError(f"{key} must be a non-empty string")
    return value


def _require_int(obj: Mapping[str, Any], key: str) -> int:
    value = obj.get(key)
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValueError(f"{key} must be an int")
    return int(value)


def authorization_from_obj(obj: Mapping[str, Any]) -> OracleAuthorization:
    return OracleAuthorization(
        consumer_module=_require_str(obj, "consumer_module"),
        action_kind=_require_str(obj, "action_kind"),
        action_id=_require_str(obj, "action_id"),
        action_facts_hash=_require_str(obj, "action_facts_hash"),
        pre_state_hash=_require_str(obj, "pre_state_hash"),
        profile_id=_require_str(obj, "profile_id"),
        query_id=_require_str(obj, "query_id"),
        value_e8=_require_int(obj, "value_e8"),
        value_hash=_require_str(obj, "value_hash"),
        confidence_e8=_require_int(obj, "confidence_e8"),
        deviation_bps=_require_int(obj, "deviation_bps"),
        observed_epoch=_require_int(obj, "observed_epoch"),
        expires_at_epoch=_require_int(obj, "expires_at_epoch"),
        feed_id=_require_str(obj, "feed_id"),
        feed_registry_root=_require_str(obj, "feed_registry_root"),
        query_policy_root=_require_str(obj, "query_policy_root"),
        source_registry_root=_require_str(obj, "source_registry_root"),
        reporter_registry_root=_require_str(obj, "reporter_registry_root"),
        evidence_class=_require_str(obj, "evidence_class"),
        economic_envelope_id=_require_str(obj, "economic_envelope_id"),
        receipt_graph_root=_require_str(obj, "receipt_graph_root"),
    )


def runtime_from_obj(obj: Mapping[str, Any]) -> RuntimeActionFacts:
    return RuntimeActionFacts(
        consumer_module=_require_str(obj, "consumer_module"),
        action_kind=_require_str(obj, "action_kind"),
        action_id=_require_str(obj, "action_id"),
        action_facts_hash=_require_str(obj, "action_facts_hash"),
        pre_state_hash=_require_str(obj, "pre_state_hash"),
        profile_id=_require_str(obj, "profile_id"),
        query_id=_require_str(obj, "query_id"),
        runtime_value_e8=_require_int(obj, "runtime_value_e8"),
        now_epoch=_require_int(obj, "now_epoch"),
    )


def _authorization_obj_from_payload(payload: Mapping[str, Any]) -> Mapping[str, Any]:
    maybe_nested = payload.get("authorization")
    if isinstance(maybe_nested, Mapping):
        return maybe_nested
    return payload


def check_authorization_for_runtime(
    authorization_payload: Mapping[str, Any],
    runtime: RuntimeActionFacts,
) -> dict[str, Any]:
    """Check one authorization against runtime facts supplied by the consumer.

    Critical adapters should use this shape instead of trusting a bundle's
    embedded `runtime_action`, because the adapter must compare against the
    action facts it is actually about to execute.
    """

    authorization = authorization_from_obj(_authorization_obj_from_payload(authorization_payload))
    opaque_ok, opaque_errors = verify_opaque_authorization(authorization, runtime)
    typed_ok, typed_errors = verify_typed_authorization(authorization, runtime)
    return {
        "schema": SCHEMA,
        "opaque_ok": bool(opaque_ok),
        "typed_ok": bool(typed_ok),
        "opaque_errors": list(opaque_errors),
        "typed_errors": list(typed_errors),
        "authorization": asdict(authorization),
        "runtime_action": asdict(runtime),
    }


def check_authorization_payload(payload: Mapping[str, Any]) -> dict[str, Any]:
    auth_obj = payload.get("authorization")
    runtime_obj = payload.get("runtime_action")
    if not isinstance(auth_obj, Mapping):
        raise ValueError("authorization must be an object")
    if not isinstance(runtime_obj, Mapping):
        raise ValueError("runtime_action must be an object")
    return check_authorization_for_runtime(auth_obj, runtime_from_obj(runtime_obj))


def check_critical_consumer_authorization(
    authorization_payload: Mapping[str, Any],
    *,
    consumer_module: str,
    action_kind: str,
    action_id: str,
    action_facts_hash: str,
    pre_state_hash: str,
    query_id: str,
    runtime_value_e8: int,
    now_epoch: int,
    profile_id: str | None = None,
) -> dict[str, Any]:
    expected_profile = profile_id or CRITICAL_CONSUMER_PROFILES.get((consumer_module, action_kind))
    if expected_profile is None:
        return {
            "schema": SCHEMA,
            "opaque_ok": False,
            "typed_ok": False,
            "opaque_errors": ["unsupported critical consumer/action"],
            "typed_errors": ["unsupported critical consumer/action"],
            "authorization": dict(_authorization_obj_from_payload(authorization_payload)),
            "runtime_action": {
                "consumer_module": consumer_module,
                "action_kind": action_kind,
                "action_id": action_id,
                "action_facts_hash": action_facts_hash,
                "pre_state_hash": pre_state_hash,
                "profile_id": profile_id,
                "query_id": query_id,
                "runtime_value_e8": runtime_value_e8,
                "now_epoch": now_epoch,
            },
        }
    runtime = RuntimeActionFacts(
        consumer_module=consumer_module,
        action_kind=action_kind,
        action_id=action_id,
        action_facts_hash=action_facts_hash,
        pre_state_hash=pre_state_hash,
        profile_id=expected_profile,
        query_id=query_id,
        runtime_value_e8=int(runtime_value_e8),
        now_epoch=int(now_epoch),
    )
    result = check_authorization_for_runtime(authorization_payload, runtime)
    authorization = authorization_from_obj(_authorization_obj_from_payload(authorization_payload))
    typed_errors = list(result["typed_errors"])
    if authorization.profile_id != expected_profile:
        typed_errors.append("critical profile mismatch")
    result["typed_errors"] = typed_errors
    result["typed_ok"] = bool(result["typed_ok"] and not typed_errors)
    result["critical_consumer_profile"] = expected_profile
    return result
