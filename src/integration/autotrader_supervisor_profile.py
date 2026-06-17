"""Bounded supervisor-profile preflight for mounted AutoTrader automation.

This module describes a narrowly scoped local/testnet supervisor posture for
manual operator-driven ticks. It does not claim unattended production
automation, wallet custody, or production chain submission.
"""

from __future__ import annotations

from typing import Any, Mapping

from src.integration.zeno_ledger_v0 import hash_v0

AUTOTRADER_SUPERVISOR_PROFILE_SCHEMA_V1 = "zenodex/autotrader-supervisor-profile/v1"
AUTOTRADER_SUPERVISOR_STATUS_SCHEMA_V1 = "zenodex/autotrader-supervisor-status/v1"
AUTOTRADER_SUPERVISOR_EXECUTION_MODE = "bounded_local_testnet_supervisor"

_NON_HASH_FIELDS = frozenset({"supervisor_hash"})
_NOT_CLAIMED = (
    "does_not_claim_unattended_production_execution",
    "does_not_claim_production_wallet_custody",
    "does_not_claim_production_chain_submission",
    "does_not_claim_scheduler_fairness",
)
_PROFILE_PARSE_ERRORS = (TypeError, ValueError)


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_nonempty_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{name} must be a non-empty string")
    return value.strip()


def _require_bool(value: object, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return bool(value)


def _require_positive_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise ValueError(f"{name} must be a positive int")
    return int(value)


def _require_string_list(value: object, *, name: str) -> list[str]:
    if not isinstance(value, list) or not value:
        raise TypeError(f"{name} must be a non-empty list")
    out: list[str] = []
    for index, item in enumerate(value):
        if not isinstance(item, str) or not item.strip():
            raise ValueError(f"{name}[{index}] must be a non-empty string")
        out.append(item.strip())
    return out


def _body(profile: Mapping[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in dict(profile).items() if key not in _NON_HASH_FIELDS}


def autotrader_supervisor_profile_hash_v1(profile: Mapping[str, Any]) -> str:
    return hash_v0("autotrader_supervisor_profile_v1", _body(profile))


def build_autotrader_supervisor_profile_v1(
    *,
    supervisor_id: str,
    chain_id: str,
    stage: str,
    enabled: bool,
    execution_mode: str = AUTOTRADER_SUPERVISOR_EXECUTION_MODE,
    external_signed_payload_required: bool,
    execution_id_required: bool,
    release_certificate_required: bool,
    stage_certificate_required: bool,
    require_testnet_submission: bool,
    require_local_preparation: bool,
    max_actions_per_tick: int,
    max_runs_per_process: int,
    allowed_templates: list[str],
    allowed_actions: list[str],
) -> dict[str, Any]:
    body = {
        "schema": AUTOTRADER_SUPERVISOR_PROFILE_SCHEMA_V1,
        "supervisor_id": _require_nonempty_str(supervisor_id, name="supervisor_id"),
        "chain_id": _require_nonempty_str(chain_id, name="chain_id"),
        "stage": _require_nonempty_str(stage, name="stage"),
        "enabled": bool(enabled),
        "execution_mode": _require_nonempty_str(execution_mode, name="execution_mode"),
        "external_signed_payload_required": _require_bool(
            external_signed_payload_required,
            name="external_signed_payload_required",
        ),
        "execution_id_required": _require_bool(execution_id_required, name="execution_id_required"),
        "release_certificate_required": _require_bool(
            release_certificate_required,
            name="release_certificate_required",
        ),
        "stage_certificate_required": _require_bool(
            stage_certificate_required,
            name="stage_certificate_required",
        ),
        "require_testnet_submission": _require_bool(
            require_testnet_submission,
            name="require_testnet_submission",
        ),
        "require_local_preparation": _require_bool(
            require_local_preparation,
            name="require_local_preparation",
        ),
        "max_actions_per_tick": _require_positive_int(
            max_actions_per_tick,
            name="max_actions_per_tick",
        ),
        "max_runs_per_process": _require_positive_int(
            max_runs_per_process,
            name="max_runs_per_process",
        ),
        "allowed_templates": _require_string_list(allowed_templates, name="allowed_templates"),
        "allowed_actions": _require_string_list(allowed_actions, name="allowed_actions"),
    }
    return {**body, "supervisor_hash": autotrader_supervisor_profile_hash_v1(body)}


def evaluate_autotrader_supervisor_profile_v1(
    profile: Mapping[str, Any] | None,
    *,
    expected_chain_id: str | None = None,
) -> dict[str, Any]:
    gaps: list[str] = []
    if profile is None:
        gaps.append("autotrader supervisor profile is missing")
        return _status(
            ok=False,
            profile=None,
            readiness_gaps=gaps,
            expected_chain_id=expected_chain_id,
        )

    try:
        obj = _require_mapping(profile, name="profile")
    except _PROFILE_PARSE_ERRORS as exc:
        gaps.append(f"autotrader supervisor profile invalid: {exc}")
        return _status(
            ok=False,
            profile=None,
            readiness_gaps=gaps,
            expected_chain_id=expected_chain_id,
        )

    try:
        schema = _require_nonempty_str(obj.get("schema"), name="schema")
        supervisor_id = _require_nonempty_str(obj.get("supervisor_id"), name="supervisor_id")
        chain_id = _require_nonempty_str(obj.get("chain_id"), name="chain_id")
        stage = _require_nonempty_str(obj.get("stage"), name="stage")
        execution_mode = _require_nonempty_str(obj.get("execution_mode"), name="execution_mode")
        enabled = _require_bool(obj.get("enabled"), name="enabled")
        external_signed_payload_required = _require_bool(
            obj.get("external_signed_payload_required"),
            name="external_signed_payload_required",
        )
        execution_id_required = _require_bool(
            obj.get("execution_id_required"),
            name="execution_id_required",
        )
        release_certificate_required = _require_bool(
            obj.get("release_certificate_required"),
            name="release_certificate_required",
        )
        stage_certificate_required = _require_bool(
            obj.get("stage_certificate_required"),
            name="stage_certificate_required",
        )
        require_testnet_submission = _require_bool(
            obj.get("require_testnet_submission"),
            name="require_testnet_submission",
        )
        require_local_preparation = _require_bool(
            obj.get("require_local_preparation"),
            name="require_local_preparation",
        )
        max_actions_per_tick = _require_positive_int(
            obj.get("max_actions_per_tick"),
            name="max_actions_per_tick",
        )
        max_runs_per_process = _require_positive_int(
            obj.get("max_runs_per_process"),
            name="max_runs_per_process",
        )
        allowed_templates = _require_string_list(
            obj.get("allowed_templates"),
            name="allowed_templates",
        )
        allowed_actions = _require_string_list(
            obj.get("allowed_actions"),
            name="allowed_actions",
        )
    except _PROFILE_PARSE_ERRORS as exc:
        gaps.append(str(exc))
        return _status(
            ok=False,
            profile=obj,
            readiness_gaps=gaps,
            expected_chain_id=expected_chain_id,
        )

    if schema != AUTOTRADER_SUPERVISOR_PROFILE_SCHEMA_V1:
        gaps.append("autotrader supervisor profile schema mismatch")
    if expected_chain_id is not None and chain_id != expected_chain_id:
        gaps.append("autotrader supervisor profile chain_id mismatch")
    if obj.get("supervisor_hash") != autotrader_supervisor_profile_hash_v1(obj):
        gaps.append("autotrader supervisor profile hash mismatch")
    if enabled is not True:
        gaps.append("autotrader supervisor profile must be enabled")
    if execution_mode != AUTOTRADER_SUPERVISOR_EXECUTION_MODE:
        gaps.append("autotrader supervisor execution_mode mismatch")
    if external_signed_payload_required is not True:
        gaps.append("autotrader supervisor must require externally signed payloads")
    if execution_id_required is not True:
        gaps.append("autotrader supervisor must require execution ids")
    if release_certificate_required is not True:
        gaps.append("autotrader supervisor must require release certificates")
    if stage_certificate_required is not True:
        gaps.append("autotrader supervisor must require stage certificates")
    if require_testnet_submission is not True:
        gaps.append("autotrader supervisor must require local/testnet submission gating")
    if require_local_preparation is not True:
        gaps.append("autotrader supervisor must require local preparation gating")
    if max_actions_per_tick > 4:
        gaps.append("autotrader supervisor max_actions_per_tick must be <= 4")
    if "dca" not in allowed_templates:
        gaps.append("autotrader supervisor allowed_templates must include dca")
    if "PLACE_SWAP_EXACT_IN" not in allowed_actions:
        gaps.append("autotrader supervisor allowed_actions must include PLACE_SWAP_EXACT_IN")

    return _status(
        ok=not gaps,
        profile={
            "schema": schema,
            "supervisor_id": supervisor_id,
            "chain_id": chain_id,
            "stage": stage,
            "execution_mode": execution_mode,
            "enabled": enabled,
            "external_signed_payload_required": external_signed_payload_required,
            "execution_id_required": execution_id_required,
            "release_certificate_required": release_certificate_required,
            "stage_certificate_required": stage_certificate_required,
            "require_testnet_submission": require_testnet_submission,
            "require_local_preparation": require_local_preparation,
            "max_actions_per_tick": max_actions_per_tick,
            "max_runs_per_process": max_runs_per_process,
            "allowed_templates": allowed_templates,
            "allowed_actions": allowed_actions,
            "supervisor_hash": obj.get("supervisor_hash"),
        },
        readiness_gaps=gaps,
        expected_chain_id=expected_chain_id,
    )


def _status(
    *,
    ok: bool,
    profile: Mapping[str, Any] | None,
    readiness_gaps: list[str],
    expected_chain_id: str | None,
) -> dict[str, Any]:
    def _status_int(key: str) -> int:
        if profile is None:
            return 0
        value = profile.get(key, 0)
        if not isinstance(value, int) or isinstance(value, bool):
            return 0
        return int(value)

    def _status_list(key: str) -> list[Any]:
        if profile is None:
            return []
        value = profile.get(key, [])
        if not isinstance(value, list):
            return []
        return list(value)

    return {
        "schema": AUTOTRADER_SUPERVISOR_STATUS_SCHEMA_V1,
        "ok": bool(ok),
        "supervisor_ready": bool(ok),
        "status": "ready" if ok else "blocked",
        "expected_chain_id": expected_chain_id,
        "supervisor_id": None if profile is None else profile.get("supervisor_id"),
        "chain_id": None if profile is None else profile.get("chain_id"),
        "stage": None if profile is None else profile.get("stage"),
        "execution_mode": None if profile is None else profile.get("execution_mode"),
        "enabled": bool(False if profile is None else profile.get("enabled")),
        "external_signed_payload_required": bool(
            False if profile is None else profile.get("external_signed_payload_required")
        ),
        "execution_id_required": bool(False if profile is None else profile.get("execution_id_required")),
        "release_certificate_required": bool(
            False if profile is None else profile.get("release_certificate_required")
        ),
        "stage_certificate_required": bool(
            False if profile is None else profile.get("stage_certificate_required")
        ),
        "require_testnet_submission": bool(
            False if profile is None else profile.get("require_testnet_submission")
        ),
        "require_local_preparation": bool(
            False if profile is None else profile.get("require_local_preparation")
        ),
        "max_actions_per_tick": _status_int("max_actions_per_tick"),
        "max_runs_per_process": _status_int("max_runs_per_process"),
        "allowed_templates": _status_list("allowed_templates"),
        "allowed_actions": _status_list("allowed_actions"),
        "supervisor_hash": None if profile is None else profile.get("supervisor_hash"),
        "readiness_gaps": list(readiness_gaps),
        "not_claimed": list(_NOT_CLAIMED),
    }
