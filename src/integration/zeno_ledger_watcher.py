"""Watcher attestations for independently verified ZenoLedger ranges."""

from __future__ import annotations

from typing import Any, Mapping

from src.integration.zeno_ledger_profile import (
    ZERO_ROOT_V0,
    validate_zeno_ledger_profile_v0,
)
from src.integration.zeno_ledger_app_hash_history import (
    app_hash_history_merkle_root_v0,
    checked_range_hash_v0,
    checked_range_summary_v0,
    validate_checked_range_summary_v0,
)
from src.integration.zeno_ledger_v0 import hash_v0
from src.state.canonical import canonical_hex_fixed_allow_0x


WATCHER_ATTESTATION_SCHEMA_V0 = "zenodex/zeno_ledger/watcher_attestation/v0"
COMPACT_WATCHER_ATTESTATION_SCHEMA_V0 = "zenodex/zeno_ledger/compact_watcher_attestation/v0"
WATCHER_ATTESTATION_STATUS_V0 = "range_verified"
CompactVerifyReportV0 = Mapping[str, Any]
WatcherAttestationV0 = Mapping[str, Any]


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
    if report.get("ok") is not True or report.get("status") != "accepted":
        raise ValueError("verify_report must be accepted")
    errors = report.get("errors")
    if errors != []:
        raise ValueError("verify_report errors must be empty")
    _require_root(report.get("last_header_hash"), name="verify_report.last_header_hash")
    _require_root(report.get("last_post_state_root"), name="verify_report.last_post_state_root")
    _require_root(report.get("last_app_hash"), name="verify_report.last_app_hash")
    return _checked_height_range(report)


def _validate_successful_compact_verify_report(verify_report: Mapping[str, Any]) -> Mapping[str, int]:
    report = _require_mapping(verify_report, name="verify_report")
    if report.get("schema") != "zenodex.zeno_ledger.verify_report.v0":
        raise ValueError("verify_report schema mismatch")
    if report.get("ok") is not True or report.get("status") != "accepted":
        raise ValueError("verify_report must be accepted")
    errors = report.get("errors")
    if errors != []:
        raise ValueError("verify_report errors must be empty")
    _require_root(report.get("last_header_hash"), name="verify_report.last_header_hash")
    _require_root(report.get("last_post_state_root"), name="verify_report.last_post_state_root")
    _require_root(report.get("last_app_hash"), name="verify_report.last_app_hash")
    checked_range = validate_checked_range_summary_v0(
        _require_mapping(report.get("checked_range"), name="verify_report.checked_range"),
        name="verify_report.checked_range",
    )
    expected_range_hash = checked_range_hash_v0(checked_range)
    actual_range_hash = _require_root(report.get("checked_range_hash"), name="verify_report.checked_range_hash")
    if actual_range_hash != expected_range_hash:
        raise ValueError("verify_report.checked_range_hash mismatch")
    return checked_range


def compact_verify_report_v0(verify_report: Mapping[str, Any]) -> CompactVerifyReportV0:
    """Return the canonical compact range view of an accepted verify report."""

    report = dict(_require_mapping(verify_report, name="verify_report"))
    if "checked_heights" in report:
        _from_height, _to_height, checked_heights = _validate_successful_verify_report(report)
        checked_range = checked_range_summary_v0(checked_heights)
        if "checked_range" in report:
            supplied_range = validate_checked_range_summary_v0(
                _require_mapping(report.get("checked_range"), name="verify_report.checked_range"),
                name="verify_report.checked_range",
            )
            if dict(supplied_range) != dict(checked_range):
                raise ValueError("verify_report.checked_range mismatch")
        if "checked_range_hash" in report:
            supplied_hash = _require_root(report.get("checked_range_hash"), name="verify_report.checked_range_hash")
            if supplied_hash != checked_range_hash_v0(checked_range):
                raise ValueError("verify_report.checked_range_hash mismatch")
        if "app_hashes_by_height" in report and "app_hash_history_root" in report:
            supplied_history_root = _require_root(
                report.get("app_hash_history_root"),
                name="verify_report.app_hash_history_root",
            )
            if supplied_history_root != app_hash_history_merkle_root_v0(report["app_hashes_by_height"]):
                raise ValueError("verify_report.app_hash_history_root mismatch")
    else:
        checked_range = _validate_successful_compact_verify_report(report)

    compact = {
        key: value
        for key, value in report.items()
        if key not in {"checked_heights", "app_hashes_by_height"}
    }
    compact["checked_range"] = dict(checked_range)
    compact["checked_range_hash"] = checked_range_hash_v0(checked_range)
    return compact


def build_watcher_attestation_v0(
    *,
    verify_report: Mapping[str, Any],
    watcher_id: str,
    observed_time_ms: int,
    verifier_ref: str,
    profile: Mapping[str, Any] | None = None,
) -> WatcherAttestationV0:
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


def build_compact_watcher_attestation_v0(
    *,
    verify_report: Mapping[str, Any],
    watcher_id: str,
    observed_time_ms: int,
    verifier_ref: str,
    profile: Mapping[str, Any] | None = None,
) -> WatcherAttestationV0:
    """Build a watcher attestation over a compact checked-range report."""

    report = compact_verify_report_v0(verify_report)
    checked_range = _validate_successful_compact_verify_report(report)
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
        "schema": COMPACT_WATCHER_ATTESTATION_SCHEMA_V0,
        "status": WATCHER_ATTESTATION_STATUS_V0,
        "watcher_id": watcher,
        "observed_time_ms": observed_ms,
        "verifier_ref": verifier,
        "profile_id": profile_id,
        "profile_name": profile_name,
        "deployment_mode": deployment_mode,
        "chain_id": chain_id,
        "from_height": checked_range["from_height"],
        "to_height": checked_range["to_height"],
        "height_count": checked_range["height_count"],
        "checked_range_hash": report["checked_range_hash"],
        "last_header_hash": report["last_header_hash"],
        "last_post_state_root": report["last_post_state_root"],
        "last_app_hash": report["last_app_hash"],
        "verify_report_hash": hash_v0("compact_verify_report_v0", report),
    }
    return {**body, "attestation_hash": hash_v0("compact_watcher_attestation_v0", body)}


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


def validate_compact_watcher_attestation_v0(
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
    expected = build_compact_watcher_attestation_v0(
        verify_report=verify_report,
        watcher_id=watcher_id,
        observed_time_ms=observed_time_ms,
        verifier_ref=verifier_ref,
        profile=profile,
    )
    if dict(obj) != expected:
        raise ValueError("compact watcher attestation binding mismatch")
