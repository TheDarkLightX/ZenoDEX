"""Public testnet status objects for ZenoLedger mirrors and watchers."""

from __future__ import annotations

from pathlib import Path
from typing import Any, Mapping, Sequence

from src.integration.zeno_ledger_feature_suite import validate_feature_suite_manifest_v0
from src.integration.zeno_ledger_mirror import validate_mirror_index_v0
from src.integration.zeno_ledger_signer_registry import SIGNATURE_QUORUM_REPORT_SCHEMA_V0
from src.integration.zeno_ledger_v0 import hash_v0
from src.integration.zeno_ledger_watcher import WATCHER_ATTESTATION_SCHEMA_V0


TESTNET_STATUS_SCHEMA_V0 = "zenodex/zeno_ledger/testnet_status/v0"
FEATURE_SUITE_RUN_REPORT_SCHEMA_V0 = "zenodex.zeno_ledger.run_feature_suite_report.v0"


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
    return int(value)


def _validate_watcher_attestation_hash(attestation: Mapping[str, Any]) -> None:
    obj = _require_mapping(attestation, name="watcher_attestation")
    if obj.get("schema") != WATCHER_ATTESTATION_SCHEMA_V0:
        raise ValueError("watcher attestation schema mismatch")
    attestation_hash = _require_str(obj.get("attestation_hash"), name="attestation_hash")
    body = {key: value for key, value in obj.items() if key != "attestation_hash"}
    expected = hash_v0("watcher_attestation_v0", body)
    if attestation_hash != expected:
        raise ValueError("watcher attestation hash mismatch")


def _validate_quorum_report_hash(quorum_report: Mapping[str, Any]) -> None:
    obj = _require_mapping(quorum_report, name="quorum_report")
    if obj.get("schema") != SIGNATURE_QUORUM_REPORT_SCHEMA_V0:
        raise ValueError("quorum report schema mismatch")
    quorum_hash = _require_str(obj.get("quorum_report_hash"), name="quorum_report_hash")
    body = {key: value for key, value in obj.items() if key != "quorum_report_hash"}
    expected = hash_v0("signature_quorum_report_v0", body)
    if quorum_hash != expected:
        raise ValueError("quorum report hash mismatch")


def _feature_suite_summary(feature_suite: Mapping[str, Any] | None) -> dict[str, Any] | None:
    if feature_suite is None:
        return None
    obj = dict(_require_mapping(feature_suite, name="feature_suite"))
    validate_feature_suite_manifest_v0(obj)
    return {
        "feature_suite_hash": obj["feature_suite_hash"],
        "feature_count": obj["feature_count"],
        "required_features": list(obj["required_features"]),
        "feature_ids": [str(item["feature_id"]) for item in obj["features"]],
    }


def _feature_suite_run_summary(run_report: Mapping[str, Any] | None) -> dict[str, Any] | None:
    if run_report is None:
        return None
    obj = _require_mapping(run_report, name="feature_suite_run_report")
    if obj.get("schema") != FEATURE_SUITE_RUN_REPORT_SCHEMA_V0:
        raise ValueError("feature suite run report schema mismatch")
    if obj.get("ok") is not True or obj.get("status") != "accepted":
        raise ValueError("feature suite run report must be accepted")
    covered = obj.get("covered_features")
    if not isinstance(covered, list) or not all(isinstance(item, str) and item for item in covered):
        raise ValueError("covered_features must be a non-empty string list")
    return {
        "feature_suite_hash": _require_str(obj.get("feature_suite_hash"), name="feature_suite_hash"),
        "covered_features": list(covered),
        "covered_feature_count": len(covered),
    }


def build_testnet_status_v0(
    *,
    network_id: str,
    mirror_index: Mapping[str, Any],
    mirror_root: Path,
    watcher_attestations: Sequence[Mapping[str, Any]],
    feature_suite: Mapping[str, Any] | None = None,
    feature_suite_run_report: Mapping[str, Any] | None = None,
    quorum_reports: Sequence[Mapping[str, Any]] = (),
) -> dict[str, Any]:
    network = _require_str(network_id, name="network_id")
    mirror_obj = dict(_require_mapping(mirror_index, name="mirror_index"))
    validate_mirror_index_v0(index=mirror_obj, mirror_root=mirror_root)
    if not watcher_attestations:
        raise ValueError("at least one watcher attestation is required")
    watcher_entries: list[dict[str, Any]] = []
    for index, raw in enumerate(watcher_attestations):
        attestation = _require_mapping(raw, name=f"watcher_attestations[{index}]")
        _validate_watcher_attestation_hash(attestation)
        watcher_entries.append(
            {
                "watcher_id": _require_str(attestation.get("watcher_id"), name=f"watcher_attestations[{index}].watcher_id"),
                "from_height": _require_nonnegative_int(attestation.get("from_height"), name=f"watcher_attestations[{index}].from_height"),
                "to_height": _require_nonnegative_int(attestation.get("to_height"), name=f"watcher_attestations[{index}].to_height"),
                "last_header_hash": _require_str(
                    attestation.get("last_header_hash"),
                    name=f"watcher_attestations[{index}].last_header_hash",
                ),
                "last_app_hash": _require_str(
                    attestation.get("last_app_hash"),
                    name=f"watcher_attestations[{index}].last_app_hash",
                ),
                "attestation_hash": _require_str(
                    attestation.get("attestation_hash"),
                    name=f"watcher_attestations[{index}].attestation_hash",
                ),
            }
        )
    watcher_entries.sort(key=lambda item: (item["watcher_id"], item["from_height"], item["to_height"]))
    watcher_range_root: tuple[int, int, str, str] | None = None
    for entry in watcher_entries:
        current = (
            int(entry["from_height"]),
            int(entry["to_height"]),
            str(entry["last_header_hash"]),
            str(entry["last_app_hash"]),
        )
        if watcher_range_root is None:
            watcher_range_root = current
        elif current != watcher_range_root:
            raise ValueError("watcher attestations must agree on range and final roots")

    quorum_entries: list[dict[str, Any]] = []
    for index, raw in enumerate(quorum_reports):
        report = _require_mapping(raw, name=f"quorum_reports[{index}]")
        _validate_quorum_report_hash(report)
        quorum_entries.append(
            {
                "payload_kind": _require_str(report.get("payload_kind"), name=f"quorum_reports[{index}].payload_kind"),
                "payload_hash": _require_str(report.get("payload_hash"), name=f"quorum_reports[{index}].payload_hash"),
                "registry_hash": _require_str(report.get("registry_hash"), name=f"quorum_reports[{index}].registry_hash"),
                "accepted_weight": _require_nonnegative_int(
                    report.get("accepted_weight"),
                    name=f"quorum_reports[{index}].accepted_weight",
                ),
                "threshold": _require_nonnegative_int(report.get("threshold"), name=f"quorum_reports[{index}].threshold"),
                "quorum_report_hash": _require_str(
                    report.get("quorum_report_hash"),
                    name=f"quorum_reports[{index}].quorum_report_hash",
                ),
            }
        )
    quorum_entries.sort(key=lambda item: (item["payload_kind"], item["payload_hash"], item["registry_hash"]))

    feature_summary = _feature_suite_summary(feature_suite)
    run_summary = _feature_suite_run_summary(feature_suite_run_report)
    if feature_summary is not None and run_summary is not None:
        if feature_summary["feature_suite_hash"] != run_summary["feature_suite_hash"]:
            raise ValueError("feature suite run report hash mismatch")
        feature_ids = set(feature_summary["feature_ids"])
        required_features = set(feature_summary["required_features"])
        covered_features = set(run_summary["covered_features"])
        if covered_features != feature_ids:
            raise ValueError("feature suite coverage mismatch")
        if not required_features.issubset(covered_features):
            raise ValueError("required feature coverage missing")

    body = {
        "schema": TESTNET_STATUS_SCHEMA_V0,
        "network_id": network,
        "mirror_index_hash": mirror_obj["mirror_index_hash"],
        "artifact_count": mirror_obj["artifact_count"],
        "watcher_count": len(watcher_entries),
        "watchers": watcher_entries,
        "feature_suite": feature_summary,
        "feature_suite_run": run_summary,
        "quorum_report_count": len(quorum_entries),
        "quorum_reports": quorum_entries,
    }
    return {**body, "testnet_status_hash": hash_v0("testnet_status_v0", body)}


def validate_testnet_status_v0(
    *,
    status: Mapping[str, Any],
    mirror_index: Mapping[str, Any],
    mirror_root: Path,
    watcher_attestations: Sequence[Mapping[str, Any]],
    feature_suite: Mapping[str, Any] | None = None,
    feature_suite_run_report: Mapping[str, Any] | None = None,
    quorum_reports: Sequence[Mapping[str, Any]] = (),
) -> None:
    obj = _require_mapping(status, name="status")
    if obj.get("schema") != TESTNET_STATUS_SCHEMA_V0:
        raise ValueError("testnet status schema mismatch")
    expected = build_testnet_status_v0(
        network_id=_require_str(obj.get("network_id"), name="network_id"),
        mirror_index=mirror_index,
        mirror_root=mirror_root,
        watcher_attestations=watcher_attestations,
        feature_suite=feature_suite,
        feature_suite_run_report=feature_suite_run_report,
        quorum_reports=quorum_reports,
    )
    if dict(obj) != expected:
        raise ValueError("testnet status binding mismatch")
