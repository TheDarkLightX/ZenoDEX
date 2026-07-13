"""Watcher attestations for independently verified ZenoLedger ranges."""

from __future__ import annotations

from typing import Any, Mapping

from src.integration.zeno_ledger_profile import (
    ZERO_ROOT_V0,
    validate_zeno_ledger_profile_v0,
)
from src.integration.zeno_ledger_v0 import hash_v0
from src.state.canonical import canonical_hex_fixed_allow_0x

WATCHER_ATTESTATION_SCHEMA_V0 = "zenodex/zeno_ledger/watcher_attestation/v0"
WATCHER_ATTESTATION_STATUS_V0 = "range_verified"
REPLAY_BOUND_VERIFY_MODE_V0 = "replay_bound"
REPLAY_BOUND_AUTHORITY_SCOPE_V0 = "replay_bound_range_v0"
REPLAY_BOUND_FACTS_V0 = (
    "range_verified",
    "header_linkage_checked",
    "state_continuity_checked",
    "state_replay_checked",
    "receipt_replay_checked",
    "config_binding_checked",
)


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a non-negative int")
    return value


def _require_root(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    return canonical


def _checked_height_range(verify_report: Mapping[str, Any]) -> tuple[int, int, list[int]]:
    checked = verify_report.get("checked_heights")
    if not isinstance(checked, list) or not checked:
        raise ValueError("verify_report.checked_heights must be a non-empty list")
    heights: list[int] = []
    for index, item in enumerate(checked):
        height = _require_nonnegative_int(item, name=f"verify_report.checked_heights[{index}]")
        if index > 0 and height != heights[-1] + 1:
            raise ValueError("verify_report.checked_heights must be contiguous")
        heights.append(height)
    return heights[0], heights[-1], heights


def _validate_successful_verify_report(verify_report: Mapping[str, Any]) -> tuple[int, int, list[int]]:
    report = _require_mapping(verify_report, name="verify_report")
    if report.get("schema") != "zenodex.zeno_ledger.verify_report.v0":
        raise ValueError("verify_report schema mismatch")
    if (
        report.get("ok") is not True
        or report.get("status") != WATCHER_ATTESTATION_STATUS_V0
        or report.get("mode") != REPLAY_BOUND_VERIFY_MODE_V0
        or report.get("authority_scope") != REPLAY_BOUND_AUTHORITY_SCOPE_V0
    ):
        raise ValueError("verify_report must record replay-bound range verification")
    for field in REPLAY_BOUND_FACTS_V0:
        if report.get(field) is not True:
            raise ValueError(f"verify_report.{field} must be true")
    errors = report.get("errors")
    if errors != []:
        raise ValueError("verify_report errors must be empty")
    _require_root(report.get("replay_config_digest"), name="verify_report.replay_config_digest")
    _require_root(report.get("last_header_hash"), name="verify_report.last_header_hash")
    _require_root(report.get("last_post_state_root"), name="verify_report.last_post_state_root")
    _require_root(report.get("last_app_hash"), name="verify_report.last_app_hash")
    return _checked_height_range(report)


def build_watcher_attestation_v0(
    *,
    verify_report: Mapping[str, Any],
    watcher_id: str,
    observed_time_ms: int,
    verifier_ref: str,
    profile: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Build a deterministic watcher attestation from an accepted verifier report."""

    report = dict(_require_mapping(verify_report, name="verify_report"))
    from_height, to_height, checked_heights = _validate_successful_verify_report(report)
    watcher = _require_str(watcher_id, name="watcher_id")
    verifier = _require_str(verifier_ref, name="verifier_ref")
    observed_ms = _require_nonnegative_int(observed_time_ms, name="observed_time_ms")

    profile_id = ZERO_ROOT_V0
    profile_name = ""
    deployment_mode = ""
    chain_id = ""
    if profile is not None:
        profile_obj = dict(_require_mapping(profile, name="profile"))
        validate_zeno_ledger_profile_v0(profile_obj)
        profile_id = _require_root(profile_obj["profile_id"], name="profile.profile_id")
        profile_name = str(profile_obj["profile_name"])
        deployment_mode = str(profile_obj["deployment_mode"])
        chain_id = str(profile_obj["chain_id"])

    body = {
        "schema": WATCHER_ATTESTATION_SCHEMA_V0,
        "status": WATCHER_ATTESTATION_STATUS_V0,
        "watcher_id": watcher,
        "observed_time_ms": observed_ms,
        "verifier_ref": verifier,
        "profile_id": profile_id,
        "profile_name": profile_name,
        "deployment_mode": deployment_mode,
        "chain_id": chain_id,
        "from_height": from_height,
        "to_height": to_height,
        "checked_heights": checked_heights,
        "last_header_hash": report["last_header_hash"],
        "last_post_state_root": report["last_post_state_root"],
        "last_app_hash": report["last_app_hash"],
        "verify_report_hash": hash_v0("verify_report_v0", report),
    }
    return {**body, "attestation_hash": hash_v0("watcher_attestation_v0", body)}


def validate_watcher_attestation_v0(
    *,
    attestation: Mapping[str, Any],
    verify_report: Mapping[str, Any],
    profile: Mapping[str, Any] | None = None,
) -> None:
    obj = _require_mapping(attestation, name="attestation")
    watcher_id = obj.get("watcher_id")
    observed_time_ms = obj.get("observed_time_ms")
    verifier_ref = obj.get("verifier_ref")
    if not isinstance(watcher_id, str) or watcher_id == "":
        raise ValueError("attestation watcher_id must be a non-empty string")
    if not isinstance(verifier_ref, str) or verifier_ref == "":
        raise ValueError("attestation verifier_ref must be a non-empty string")
    if not isinstance(observed_time_ms, int) or isinstance(observed_time_ms, bool) or observed_time_ms < 0:
        raise ValueError("attestation observed_time_ms must be a non-negative int")
    expected = build_watcher_attestation_v0(
        verify_report=verify_report,
        watcher_id=watcher_id,
        observed_time_ms=observed_time_ms,
        verifier_ref=verifier_ref,
        profile=profile,
    )
    if dict(obj) != expected:
        raise ValueError("watcher attestation binding mismatch")
