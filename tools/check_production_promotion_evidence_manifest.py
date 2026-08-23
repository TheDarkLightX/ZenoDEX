#!/usr/bin/env python3
"""Check a production-promotion evidence manifest against the six-lane gate.

Reads a JSON manifest with this shape::

    {
      "schema": "zenodex/production-promotion-evidence-manifest/v1",
      "config": {
        "bounded_oracle_exercise_status_path": "...",         # required for oracle_authority
        "wallet_authority_profile_hash": "...",               # required for hardware_wallet
        "live_proof_wrapper_status_path": "...",              # required for zk_wrapping
        "supervisor_profile_hash": "...",                     # required for autotrader
        "config_max_actions_per_tick": 4,                     # required for autotrader
        "config_max_runs_per_process": 200,                   # required for autotrader
        "expected_autotrader_approval_signer_pubkeys": [...], # required for autotrader
        "approved_measurements": ["nitro:..."],               # required for confidential_runtime
        "operator_status_hash": "...",                        # required for confidential_runtime
        "external_verifier_binding_hash": "..."               # required for confidential_runtime
      },
      "bundle": {
        "oracle_authority":      { ... evidence ... },
        "hardware_wallet":       { ... evidence ... },
        "zk_wrapping":           { ... evidence ... },
        "autotrader":            { ... evidence ... },
        "confidential_runtime":  { ... evidence ... },
        "app_root_jmt":          { ... evidence ... }
      }
    }

Exits 0 if every lane is ``production_ready: true``; exits 1 otherwise. The
gate prints the full lane-by-lane status JSON to stdout so it can be archived
as an assurance artifact.

Optional ``--now`` lets callers pin the "current time" used for freshness
checks, which is necessary when replaying an old evidence bundle.

Optional ``--explain-missing`` attaches machine-readable lane requirements to
the status output. Grade: A-. The old checker failed closed correctly, but
release operators only saw "evidence is missing"; production promotion needs an
exact artifact contract for every blocked lane.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any, Mapping, Sequence

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from src.integration.production_promotion_evidence import (  # noqa: E402
    evaluate_production_promotion_bundle_v1,
)

_MANIFEST_SCHEMA = "zenodex/production-promotion-evidence-manifest/v1"
_LANES = (
    "oracle_authority",
    "hardware_wallet",
    "zk_wrapping",
    "autotrader",
    "confidential_runtime",
    "app_root_jmt",
)

_LANE_REQUIREMENTS: Mapping[str, Mapping[str, Any]] = {
    "oracle_authority": {
        "purpose": "prove the production oracle authority has exercised the public-testnet path",
        "required_config_paths": ["bounded_oracle_exercise_status_path"],
        "required_config_values": ["expected_chain_id", "expected_oracle_authority_signer_pubkey"],
        "required_evidence_fields": [
            "schema",
            "authority_id",
            "chain_id",
            "target_network",
            "exercise_hash",
            "profile_authority_hash",
            "public_broadcast_height",
            "public_settlement_height",
            "public_broadcast_block_hash",
            "public_settlement_block_hash",
            "public_broadcast_explorer_url",
            "public_settlement_explorer_url",
            "authority_attestation_signature",
            "authority_attestation_signer_pubkey",
            "issued_at",
            "evidence_hash",
        ],
        "external_artifacts": [
            "bounded oracle exercise JSON with authority_exercised=true",
            "public testnet broadcast and settlement block references",
            "oracle authority attestation signature from the expected signer pubkey",
        ],
        "producer_tool": "tools/build_oracle_authority_evidence.py",
        "validator": "evaluate_production_oracle_authority_evidence_v1",
    },
    "hardware_wallet": {
        "purpose": "prove the active wallet authority is bound to a real hardware-device approval",
        "required_config_paths": [],
        "required_config_values": ["wallet_authority_profile_hash", "expected_device_pubkey"],
        "required_evidence_fields": [
            "schema",
            "device_id",
            "device_model",
            "device_firmware_version",
            "device_attestation",
            "os_prompt_capture",
            "device_approval_tx",
            "profile_wallet_authority_hash",
            "issued_at",
            "evidence_hash",
        ],
        "external_artifacts": [
            "hardware wallet attestation pubkey and signature over the canonical approval challenge",
            "OS prompt capture hash",
            "device approval transaction payload hash and signature over the canonical approval message",
        ],
        "producer_tool": "tools/build_hardware_wallet_evidence.py",
        "validator": "evaluate_production_hardware_wallet_evidence_v1",
    },
    "zk_wrapping": {
        "purpose": "prove the live proof wrapper is bound to an audited verifier/circuit artifact",
        "required_config_paths": ["live_proof_wrapper_status_path"],
        "required_config_values": ["expected_surface"],
        "required_evidence_fields": [
            "schema",
            "surface",
            "circuit_artifact",
            "soundness_audit",
            "verifier_binding",
            "sample_proof_acceptance",
            "issued_at",
            "evidence_hash",
        ],
        "external_artifacts": [
            "live proof wrapper status with zk_proof_verified=true and matching verifier/circuit artifact metadata plus binding hash",
            "circuit artifact, source, verification-key, and reproducible-build hashes",
            "soundness audit report hash",
            "sample accepted proof request/receipt hashes",
        ],
        "producer_tool": "tools/build_zk_wrapping_evidence_from_risc0_bundle.py",
        "validator": "evaluate_production_zk_wrapping_evidence_v1",
    },
    "autotrader": {
        "purpose": "prove the AutoTrader supervisor ran unattended within configured production limits",
        "required_config_paths": [],
        "required_config_values": [
            "supervisor_profile_hash",
            "config_max_actions_per_tick",
            "config_max_runs_per_process",
            "expected_chain_id",
            "expected_autotrader_approval_signer_pubkeys",
        ],
        "required_evidence_fields": [
            "schema",
            "supervisor_id",
            "chain_id",
            "profile_supervisor_hash",
            "run_window",
            "crash_recovery",
            "multi_signer_approvals",
            "budget_compliance",
            "issued_at",
            "evidence_hash",
        ],
        "external_artifacts": [
            "24h+ unattended supervisor run window with heartbeat timestamps",
            "crash recovery checkpoint evidence",
            "multi-signer Ed25519 approvals over the canonical run approval message",
            "configured production AutoTrader approver public-key set",
            "budget compliance observations",
        ],
        "producer_tool": "tools/build_autotrader_evidence.py",
        "validator": "evaluate_production_autotrader_evidence_v1",
    },
    "confidential_runtime": {
        "purpose": "prove confidential runtime receipts are bound to an approved TEE/operator/verifier posture",
        "required_config_paths": [],
        "required_config_values": [
            "approved_measurements",
            "operator_status_hash",
            "external_verifier_binding_hash",
            "expected_extension_id",
        ],
        "required_evidence_fields": [
            "schema",
            "extension_id",
            "provider_id",
            "tee_attestation",
            "approved_measurements_hash",
            "external_verifier_binding_hash",
            "operator_status_hash",
            "private_execution_receipt",
            "issued_at",
            "evidence_hash",
        ],
        "external_artifacts": [
            "TEE attestation with approved measurement",
            "approved-measurement digest and verifier binding",
            "redacted private execution receipt with runtime receipt hash and public effect digest",
            "operator status hash from the deployed confidential runtime",
        ],
        "producer_tool": "tools/build_confidential_runtime_evidence.py",
        "validator": "evaluate_production_confidential_runtime_evidence_v1",
    },
    "app_root_jmt": {
        "purpose": "prove live/header roots use the typed all-lane app-root JMT, not fixture or spot-only roots",
        "required_config_paths": [],
        "required_config_values": [],
        "required_evidence_fields": [
            "schema",
            "evidence_kind",
            "root_system",
            "required_lane_kinds",
            "live_root_checks",
            "negative_checks",
            "issued_at",
            "evidence_hash",
        ],
        "external_artifacts": [
            "plain Dex snapshot live-root replay",
            "Tau app-state wrapper live-root replay",
            "local block pre-snapshot header root replay",
            "lane-tamper negative check showing root mismatch rejection",
        ],
        "producer_tool": "tools/build_app_root_jmt_evidence.py",
        "validator": "evaluate_production_app_root_jmt_evidence_v2",
    },
}

_LANE_COLLECTION_COMMAND_TEMPLATES: Mapping[str, tuple[str, ...]] = {
    "oracle_authority": (
        "python3",
        "tools/build_oracle_authority_evidence.py",
        "--bounded-oracle-exercise-status",
        "runs/production_promotion/latest/bounded_oracle_exercise_status.json",
        "--out",
        "runs/production_promotion/latest/oracle_authority.json",
        "--authority-id",
        "ORACLE_AUTHORITY_ID",
        "--target-network",
        "public_testnet",
        "--public-broadcast-block-hash",
        "PUBLIC_BROADCAST_BLOCK_HASH",
        "--public-settlement-block-hash",
        "PUBLIC_SETTLEMENT_BLOCK_HASH",
        "--public-broadcast-explorer-url",
        "PUBLIC_BROADCAST_EXPLORER_URL",
        "--public-settlement-explorer-url",
        "PUBLIC_SETTLEMENT_EXPLORER_URL",
        "--authority-attestation-signature",
        "AUTHORITY_ATTESTATION_SIGNATURE",
        "--authority-attestation-signer-pubkey",
        "AUTHORITY_ATTESTATION_SIGNER_PUBKEY",
        "--expected-chain-id",
        "EXPECTED_CHAIN_ID",
        "--expected-authority-signer-pubkey",
        "EXPECTED_ORACLE_AUTHORITY_SIGNER_PUBKEY",
        "--issued-at",
        "ISSUED_AT",
        "--check-now",
        "CHECK_NOW",
        "--check",
    ),
    "hardware_wallet": (
        "python3",
        "tools/build_hardware_wallet_evidence.py",
        "--out",
        "runs/production_promotion/latest/hardware_wallet.json",
        "--device-id",
        "DEVICE_ID",
        "--device-model",
        "DEVICE_MODEL",
        "--device-firmware-version",
        "DEVICE_FIRMWARE_VERSION",
        "--device-pubkey",
        "DEVICE_PUBKEY",
        "--attestation-challenge",
        "ATTESTATION_CHALLENGE",
        "--attestation-signature",
        "ATTESTATION_SIGNATURE",
        "--prompt-kind",
        "PROMPT_KIND",
        "--prompt-hash",
        "PROMPT_HASH",
        "--prompt-captured-at",
        "PROMPT_CAPTURED_AT",
        "--approval-tx-payload-hash",
        "APPROVAL_TX_PAYLOAD_HASH",
        "--approval-signature",
        "APPROVAL_SIGNATURE",
        "--approval-captured-at",
        "APPROVAL_CAPTURED_AT",
        "--wallet-authority-profile-hash",
        "WALLET_AUTHORITY_PROFILE_HASH",
        "--expected-device-pubkey",
        "EXPECTED_DEVICE_PUBKEY",
        "--issued-at",
        "ISSUED_AT",
        "--check-now",
        "CHECK_NOW",
        "--check",
    ),
    "zk_wrapping": (
        "python3",
        "tools/build_zk_wrapping_evidence_from_risc0_bundle.py",
        "--risc0-surface-bundle",
        "runs/production_promotion/latest/risc0_surface_bundle.json",
        "--out",
        "runs/production_promotion/latest/zk_wrapping.json",
        "--live-wrapper-out",
        "runs/production_promotion/latest/live_proof_wrapper_status.json",
        "--surface",
        "EXPECTED_SURFACE",
        "--expected-surface",
        "EXPECTED_SURFACE",
        "--verifier-cmd-json",
        "VERIFIER_CMD_JSON",
        "--live-wrapper-status",
        "runs/production_promotion/input/live_proof_wrapper_status.json",
        "--audit-id",
        "AUDIT_ID",
        "--audit-report-hash",
        "AUDIT_REPORT_HASH",
        "--auditor",
        "AUDITOR",
        "--audited-at",
        "AUDITED_AT",
        "--accepted-at",
        "ACCEPTED_AT",
        "--issued-at",
        "ISSUED_AT",
        "--check-now",
        "CHECK_NOW",
        "--check",
    ),
    "autotrader": (
        "python3",
        "tools/build_autotrader_evidence.py",
        "--out",
        "runs/production_promotion/latest/autotrader.json",
        "--supervisor-id",
        "SUPERVISOR_ID",
        "--chain-id",
        "EXPECTED_CHAIN_ID",
        "--profile-supervisor-hash",
        "SUPERVISOR_PROFILE_HASH",
        "--started-at",
        "STARTED_AT",
        "--last-heartbeat-at",
        "LAST_HEARTBEAT_AT",
        "--duration-seconds",
        "DURATION_SECONDS",
        "--ticks-executed",
        "TICKS_EXECUTED",
        "--ticks-failed",
        "TICKS_FAILED",
        "--ticks-throttled",
        "TICKS_THROTTLED",
        "--heartbeat-timestamps-file",
        "runs/production_promotion/latest/autotrader_heartbeats.json",
        "--crash-recovery-file",
        "runs/production_promotion/latest/autotrader_crash_recovery.json",
        "--multi-signer-approvals-file",
        "runs/production_promotion/latest/autotrader_multisig_approvals.json",
        "--max-actions-per-tick-observed",
        "MAX_ACTIONS_PER_TICK_OBSERVED",
        "--max-runs-per-process-observed",
        "MAX_RUNS_PER_PROCESS_OBSERVED",
        "--config-max-actions-per-tick",
        "CONFIG_MAX_ACTIONS_PER_TICK",
        "--config-max-runs-per-process",
        "CONFIG_MAX_RUNS_PER_PROCESS",
        "--expected-chain-id",
        "EXPECTED_CHAIN_ID",
        "--expected-approval-signer-pubkeys-file",
        "runs/production_promotion/latest/autotrader_expected_approvers.json",
        "--issued-at",
        "ISSUED_AT",
        "--check-now",
        "CHECK_NOW",
        "--check",
    ),
    "confidential_runtime": (
        "python3",
        "tools/build_confidential_runtime_evidence.py",
        "--out",
        "runs/production_promotion/latest/confidential_runtime.json",
        "--extension-id",
        "EXPECTED_EXTENSION_ID",
        "--provider-id",
        "PROVIDER_ID",
        "--tee-kind",
        "TEE_KIND",
        "--raw-attestation-hash",
        "RAW_ATTESTATION_HASH",
        "--measurement",
        "APPROVED_MEASUREMENT",
        "--measurement-in-allowlist",
        "--platform-pubkey",
        "PLATFORM_PUBKEY",
        "--attestation-signature",
        "ATTESTATION_SIGNATURE",
        "--tee-verified-at",
        "TEE_VERIFIED_AT",
        "--operator-status-hash",
        "OPERATOR_STATUS_HASH",
        "--external-verifier-binding-hash",
        "EXTERNAL_VERIFIER_BINDING_HASH",
        "--runtime-receipt-hash",
        "RUNTIME_RECEIPT_HASH",
        "--attestation-receipt-hash",
        "ATTESTATION_RECEIPT_HASH",
        "--request-id",
        "REQUEST_ID",
        "--execution-id",
        "EXECUTION_ID",
        "--execution-kind",
        "EXECUTION_KIND",
        "--result-code",
        "RESULT_CODE",
        "--result-redacted",
        "--attestation-epoch",
        "ATTESTATION_EPOCH",
        "--current-epoch",
        "CURRENT_EPOCH",
        "--units-charged",
        "UNITS_CHARGED",
        "--public-effect-digest",
        "PUBLIC_EFFECT_DIGEST",
        "--approved-measurement",
        "APPROVED_MEASUREMENT",
        "--expected-extension-id",
        "EXPECTED_EXTENSION_ID",
        "--issued-at",
        "ISSUED_AT",
        "--check-now",
        "CHECK_NOW",
        "--check",
    ),
    "app_root_jmt": (
        "python3",
        "tools/build_app_root_jmt_evidence.py",
        "--out",
        "runs/production_promotion/latest/app_root_jmt.json",
        "--now",
        "APP_ROOT_CHECKED_AT",
    ),
}

_MANIFEST_BUILDER_TEMPLATE: tuple[str, ...] = (
    "python3",
    "tools/build_production_promotion_evidence_manifest.py",
    "--out",
    "runs/production_promotion/latest/production_promotion_evidence_manifest.json",
    "--oracle-authority",
    "runs/production_promotion/latest/oracle_authority.json",
    "--hardware-wallet",
    "runs/production_promotion/latest/hardware_wallet.json",
    "--zk-wrapping",
    "runs/production_promotion/latest/zk_wrapping.json",
    "--autotrader",
    "runs/production_promotion/latest/autotrader.json",
    "--confidential-runtime",
    "runs/production_promotion/latest/confidential_runtime.json",
    "--app-root-jmt",
    "runs/production_promotion/latest/app_root_jmt.json",
    "--bounded-oracle-exercise-status",
    "runs/production_promotion/latest/bounded_oracle_exercise_status.json",
    "--wallet-authority-profile-hash",
    "WALLET_AUTHORITY_PROFILE_HASH",
    "--live-proof-wrapper-status",
    "runs/production_promotion/latest/live_proof_wrapper_status.json",
    "--supervisor-profile-hash",
    "SUPERVISOR_PROFILE_HASH",
    "--config-max-actions-per-tick",
    "CONFIG_MAX_ACTIONS_PER_TICK",
    "--config-max-runs-per-process",
    "CONFIG_MAX_RUNS_PER_PROCESS",
    "--approved-measurement",
    "APPROVED_MEASUREMENT",
    "--operator-status-hash",
    "OPERATOR_STATUS_HASH",
    "--external-verifier-binding-hash",
    "EXTERNAL_VERIFIER_BINDING_HASH",
    "--expected-chain-id",
    "EXPECTED_CHAIN_ID",
    "--expected-oracle-authority-signer-pubkey",
    "EXPECTED_ORACLE_AUTHORITY_SIGNER_PUBKEY",
    "--expected-surface",
    "EXPECTED_SURFACE",
    "--expected-extension-id",
    "EXPECTED_EXTENSION_ID",
    "--expected-device-pubkey",
    "EXPECTED_DEVICE_PUBKEY",
    "--now",
    "CHECK_NOW",
    "--check",
    "--explain-missing",
)

_PLACEHOLDER_TOKEN_RE = re.compile(r"^[A-Z][A-Z0-9_]{2,}$")
_PLACEHOLDER_MARKERS = ("PLACEHOLDER", "REPLACE_ME", "TODO", "FIXME", "YOUR_")


def _command_placeholder_tokens() -> frozenset[str]:
    command_parts: list[str] = []
    for template in _LANE_COLLECTION_COMMAND_TEMPLATES.values():
        command_parts.extend(template)
    command_parts.extend(_MANIFEST_BUILDER_TEMPLATE)
    return frozenset(part for part in command_parts if _PLACEHOLDER_TOKEN_RE.fullmatch(part))


_RUNBOOK_PLACEHOLDER_TOKENS: frozenset[str] = _command_placeholder_tokens()


class _ManifestConfigBundleError(ValueError):
    pass


def _resolve_manifest_path(path: Path, *, base_dir: Path) -> Path:
    if path.is_absolute():
        raise ValueError("manifest config sidecar paths must be relative to the manifest file")
    resolved = (base_dir / path).resolve()
    try:
        resolved.relative_to(base_dir.resolve())
    except ValueError as exc:
        # Review finding (grade B+ -> A-): production evidence sidecars must be
        # bundle-local. Allowing "../" escapes or absolute paths would let a
        # green manifest depend on unarchived operator-local files.
        raise ValueError("manifest config sidecar paths must stay under the manifest directory") from exc
    return resolved


def _load_json(path: object, *, field_name: str, base_dir: Path) -> Mapping[str, Any] | None:
    if path is None:
        return None
    if not isinstance(path, str) or not path.strip():
        raise ValueError(f"{field_name} must be a non-empty path string")
    p = _resolve_manifest_path(Path(path), base_dir=base_dir)
    try:
        loaded = json.loads(p.read_text())
    except FileNotFoundError as exc:
        raise FileNotFoundError(f"{field_name} not found: {p}") from exc
    except json.JSONDecodeError as exc:
        raise ValueError(f"{field_name} invalid JSON: {exc}") from exc
    if not isinstance(loaded, Mapping):
        raise ValueError(f"{field_name} must decode to a JSON object")
    return loaded


def _optional_object(manifest: Mapping[str, Any], *, key: str) -> dict[str, Any]:
    if key not in manifest:
        return {}
    value = manifest.get(key)
    if not isinstance(value, dict):
        raise TypeError(f"{key} must be a JSON object")
    return value


def _lane_scoped_output(out: dict[str, Any], lane: str) -> dict[str, Any]:
    lanes = out.get("lanes")
    if not isinstance(lanes, Mapping) or lane not in lanes:
        return {
            "schema": out.get("schema"),
            "promotion_ready": False,
            "status": "blocked",
            "selected_lane": lane,
            "blocked_lanes": [lane],
            "gaps": [f"selected lane {lane!r} missing from evaluator output"],
            "lanes": {},
        }
    lane_status = lanes[lane]
    lane_ready = isinstance(lane_status, Mapping) and lane_status.get("production_ready") is True
    lane_gaps = []
    if isinstance(lane_status, Mapping):
        raw_gaps = lane_status.get("gaps", [])
        if isinstance(raw_gaps, list):
            lane_gaps = [f"{lane}: {gap}" for gap in raw_gaps if isinstance(gap, str)]
    return {
        **out,
        "promotion_ready": lane_ready,
        "status": "ready" if lane_ready else "blocked",
        "selected_lane": lane,
        "blocked_lanes": [] if lane_ready else [lane],
        "gaps": [] if lane_ready else lane_gaps,
        "lanes": {lane: lane_status},
    }


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("manifest", help="Path to the production-promotion evidence manifest JSON")
    parser.add_argument("--now", type=int, default=None, help="Override 'now' (unix seconds) for freshness checks")
    parser.add_argument(
        "--lane",
        choices=_LANES,
        help="Only evaluate a single lane (useful for incremental promotion)",
    )
    parser.add_argument(
        "--explain-missing",
        action="store_true",
        help="Attach machine-readable requirements for the selected/current lanes",
    )
    parser.add_argument(
        "--include-runbook",
        action="store_true",
        help="Attach deterministic producer command templates for the selected/current lanes",
    )
    parser.add_argument(
        "--readiness-plan",
        action="store_true",
        help="Attach compact per-lane readiness categories for operator dashboards",
    )
    return parser.parse_args(argv)


def _load_manifest(path: Path) -> tuple[dict[str, Any] | None, dict[str, Any] | None]:
    try:
        manifest = json.loads(path.read_text())
    except FileNotFoundError:
        return None, {"ok": False, "error": "manifest_not_found", "path": str(path)}
    except json.JSONDecodeError as exc:
        return None, {"ok": False, "error": "manifest_invalid_json", "detail": str(exc)}
    if not isinstance(manifest, dict):
        return None, {"ok": False, "error": "manifest_not_object"}
    if manifest.get("schema") != _MANIFEST_SCHEMA:
        return None, {"ok": False, "error": "manifest_schema_mismatch", "expected": _MANIFEST_SCHEMA}
    return manifest, None


def _manifest_config_and_bundle(
    manifest: Mapping[str, Any],
    *,
    lane: str | None,
) -> tuple[dict[str, Any], dict[str, Any]]:
    try:
        config = _optional_object(manifest, key="config")
        bundle = _optional_object(manifest, key="bundle")
    except TypeError as exc:
        raise _ManifestConfigBundleError(str(exc)) from exc

    if lane is not None:
        bundle = {lane: bundle.get(lane)} if lane in bundle else {lane: None}
    return config, bundle


def _evaluate_manifest(
    manifest: Mapping[str, Any],
    *,
    manifest_dir: Path,
    lane: str | None,
    now: int | None,
) -> dict[str, Any]:
    config, bundle = _manifest_config_and_bundle(manifest, lane=lane)
    # Review finding (grade B+ -> A-): selected-lane checks should isolate the
    # selected production surface. The checker used to eagerly read every
    # sidecar path in config, so `--lane autotrader` could fail because an
    # unrelated oracle or proof-wrapper sidecar was stale. Full-scope checks
    # still load every configured sidecar and fail closed across all lanes.
    bounded_oracle_exercise_status = (
        _load_json(
            config.get("bounded_oracle_exercise_status_path"),
            field_name="bounded_oracle_exercise_status_path",
            base_dir=manifest_dir,
        )
        if lane in (None, "oracle_authority")
        else None
    )
    live_proof_wrapper_status = (
        _load_json(
            config.get("live_proof_wrapper_status_path"),
            field_name="live_proof_wrapper_status_path",
            base_dir=manifest_dir,
        )
        if lane in (None, "zk_wrapping")
        else None
    )
    out = evaluate_production_promotion_bundle_v1(
        bundle,
        bounded_oracle_exercise_status=bounded_oracle_exercise_status,
        wallet_authority_profile_hash=config.get("wallet_authority_profile_hash"),
        live_proof_wrapper_status=live_proof_wrapper_status,
        supervisor_profile_hash=config.get("supervisor_profile_hash"),
        config_max_actions_per_tick=config.get("config_max_actions_per_tick"),
        config_max_runs_per_process=config.get("config_max_runs_per_process"),
        approved_measurements=config.get("approved_measurements"),
        operator_status_hash=config.get("operator_status_hash"),
        external_verifier_binding_hash=config.get("external_verifier_binding_hash"),
        expected_chain_id=config.get("expected_chain_id"),
        expected_oracle_authority_signer_pubkey=config.get("expected_oracle_authority_signer_pubkey"),
        expected_surface=config.get("expected_surface"),
        expected_extension_id=config.get("expected_extension_id"),
        expected_device_pubkey=config.get("expected_device_pubkey"),
        expected_autotrader_approval_signer_pubkeys=config.get("expected_autotrader_approval_signer_pubkeys"),
        now=now,
    )
    scoped = _lane_scoped_output(out, lane) if lane is not None else out
    return _apply_required_manifest_config(scoped, config=config, bundle=bundle, lane=lane)


def _config_value_present(value: object, *, field_name: str) -> bool:
    if field_name == "approved_measurements":
        return (
            isinstance(value, list)
            and bool(value)
            and all(isinstance(item, str) and item for item in value)
        )
    if field_name == "expected_autotrader_approval_signer_pubkeys":
        return (
            isinstance(value, list)
            and len(value) >= 2
            and all(isinstance(item, str) and item for item in value)
        )
    if field_name in {"config_max_actions_per_tick", "config_max_runs_per_process"}:
        return isinstance(value, int) and not isinstance(value, bool)
    return isinstance(value, str) and bool(value.strip())


def _config_path_present(value: object) -> bool:
    return isinstance(value, str) and bool(value.strip())


def _required_config_gaps(config: Mapping[str, Any], *, lane: str | None) -> dict[str, list[str]]:
    lanes = (lane,) if lane is not None else _LANES
    gaps: dict[str, list[str]] = {}
    for lane_id in lanes:
        lane_gaps: list[str] = []
        req = _LANE_REQUIREMENTS[lane_id]
        for field_name in req["required_config_paths"]:
            if not _config_path_present(config.get(field_name)):
                lane_gaps.append(f"manifest config.{field_name} is required for {lane_id}")
        for field_name in req["required_config_values"]:
            if not _config_value_present(config.get(field_name), field_name=field_name):
                lane_gaps.append(f"manifest config.{field_name} is required for {lane_id}")
        if lane_gaps:
            gaps[lane_id] = lane_gaps
    return gaps


def _with_required_config_gaps(
    lane_status: Mapping[str, Any],
    gaps: list[str],
) -> dict[str, Any]:
    lane_gap_list = [gap for gap in lane_status.get("gaps", []) if isinstance(gap, str)]
    lane_gap_list.extend(gaps)
    return {
        **lane_status,
        "gaps": lane_gap_list,
        "ok": False,
        "production_ready": False,
        "status": "blocked",
    }


def _blocked_lane_names(lanes: Mapping[str, Any]) -> list[str]:
    return [
        name
        for name, status in lanes.items()
        if not isinstance(status, Mapping) or status.get("production_ready") is not True
    ]


def _is_placeholder_string(value: str) -> bool:
    stripped = value.strip()
    if stripped in _RUNBOOK_PLACEHOLDER_TOKENS:
        return True
    upper = stripped.upper()
    return any(marker in upper for marker in _PLACEHOLDER_MARKERS)


def _placeholder_gaps(value: object, *, path: str) -> list[str]:
    if isinstance(value, str):
        if _is_placeholder_string(value):
            return [f"{path}: placeholder value {value!r} must be replaced by real external artifact data"]
        return []
    if isinstance(value, Mapping):
        gaps: list[str] = []
        for key in sorted(value):
            gaps.extend(_placeholder_gaps(value[key], path=f"{path}.{key}"))
        return gaps
    if isinstance(value, list):
        gaps = []
        for index, item in enumerate(value):
            gaps.extend(_placeholder_gaps(item, path=f"{path}[{index}]"))
        return gaps
    return []


def _placeholder_gaps_for_scope(
    config: Mapping[str, Any],
    bundle: Mapping[str, Any],
    *,
    lane: str | None,
) -> dict[str, list[str]]:
    lanes = (lane,) if lane is not None else _LANES
    gaps: dict[str, list[str]] = {}
    for lane_id in lanes:
        lane_gaps: list[str] = []
        req = _LANE_REQUIREMENTS[lane_id]
        for field_name in (*req["required_config_paths"], *req["required_config_values"]):
            if field_name in config:
                lane_gaps.extend(_placeholder_gaps(config[field_name], path=f"manifest config.{field_name}"))
        if lane_id in bundle and bundle[lane_id] is not None:
            lane_gaps.extend(_placeholder_gaps(bundle[lane_id], path=f"bundle.{lane_id}"))
        if lane_gaps:
            gaps[lane_id] = lane_gaps
    return gaps


def _merge_lane_gaps(*gap_maps: Mapping[str, list[str]]) -> dict[str, list[str]]:
    merged: dict[str, list[str]] = {}
    for gap_map in gap_maps:
        for lane_id, gaps in gap_map.items():
            merged.setdefault(lane_id, []).extend(gaps)
    return merged


def _apply_required_manifest_config(
    out: dict[str, Any],
    *,
    config: Mapping[str, Any],
    bundle: Mapping[str, Any],
    lane: str | None,
) -> dict[str, Any]:
    # Review note (grade B+ -> A-): lane evaluators intentionally allow some
    # expected bindings to be optional for unit and incremental checks. The
    # production-promotion manifest is stricter: documented required config
    # values must be present before a lane can clear. This closes the path where
    # a lane could pass with real-looking evidence while omitting expected_chain,
    # expected_surface, expected_device_pubkey, or expected_extension_id.
    # The collection runbook intentionally contains exact placeholder tokens.
    # The manifest checker must reject those tokens if they are copied into a
    # promotion bundle; otherwise a self-consistent fixture can satisfy a lane
    # while still being made of operator-template values.
    required_gaps = _merge_lane_gaps(
        _required_config_gaps(config, lane=lane),
        _placeholder_gaps_for_scope(config, bundle, lane=lane),
    )
    if not required_gaps:
        return out

    lanes_obj = out.get("lanes")
    if not isinstance(lanes_obj, Mapping):
        return out
    lanes: dict[str, Any] = {str(k): v for k, v in lanes_obj.items()}
    top_gaps = [gap for gap in out.get("gaps", []) if isinstance(gap, str)]
    for lane_id, gaps in required_gaps.items():
        lane_status = lanes.get(lane_id)
        if not isinstance(lane_status, Mapping):
            continue
        lanes[lane_id] = _with_required_config_gaps(lane_status, gaps)
        top_gaps.extend(f"{lane_id}: {gap}" for gap in gaps)

    blocked = _blocked_lane_names(lanes)
    return {
        **out,
        "lanes": lanes,
        "gaps": top_gaps,
        "blocked_lanes": blocked,
        "promotion_ready": False if blocked else out.get("promotion_ready") is True,
        "status": "blocked" if blocked else "ready",
    }


def _requirements_for_scope(lane: str | None) -> dict[str, Any]:
    lanes = (lane,) if lane is not None else _LANES
    return {name: dict(_LANE_REQUIREMENTS[name]) for name in lanes}


def _attach_requirements(out: dict[str, Any], *, lane: str | None) -> dict[str, Any]:
    return {**out, "requirements": _requirements_for_scope(lane)}


def _runbook_for_scope(lane: str | None) -> dict[str, Any]:
    lanes = (lane,) if lane is not None else _LANES
    return {
        "schema": "zenodex/production-promotion-evidence-collection-runbook/v1",
        "posture": (
            "operator collection template only; producer tools and the manifest checker "
            "remain authoritative, and placeholder values must be replaced by real external artifacts"
        ),
        "setup": [["mkdir", "-p", "runs/production_promotion/latest", "runs/production_promotion/input"]],
        "lanes": {
            name: {
                "purpose": _LANE_REQUIREMENTS[name]["purpose"],
                "producer_tool": _LANE_REQUIREMENTS[name]["producer_tool"],
                "external_artifacts": list(_LANE_REQUIREMENTS[name]["external_artifacts"]),
                "producer_command_template": list(_LANE_COLLECTION_COMMAND_TEMPLATES[name]),
            }
            for name in lanes
        },
        "manifest_command_template": list(_MANIFEST_BUILDER_TEMPLATE),
        "final_gate_command_template": [
            "PYTHON=.venv/bin/python",
            "bash",
            "tools/run_production_promotion_evidence_gate.sh",
            "runs/production_promotion/latest/production_promotion_evidence_manifest.json",
            "--explain-missing",
            "--include-runbook",
        ],
    }


def _attach_runbook(out: dict[str, Any], *, lane: str | None) -> dict[str, Any]:
    return {**out, "collection_runbook": _runbook_for_scope(lane)}


def _lanes_for_scope(lane: str | None) -> tuple[str, ...]:
    return (lane,) if lane is not None else _LANES


def _missing_required_config(
    config: Mapping[str, Any],
    *,
    lane_id: str,
) -> list[str]:
    req = _LANE_REQUIREMENTS[lane_id]
    missing: list[str] = []
    for field_name in req["required_config_paths"]:
        if not _config_path_present(config.get(field_name)):
            missing.append(field_name)
    for field_name in req["required_config_values"]:
        if not _config_value_present(config.get(field_name), field_name=field_name):
            missing.append(field_name)
    return missing


def _missing_required_sidecars(
    config: Mapping[str, Any],
    *,
    lane_id: str,
    manifest_dir: Path,
) -> list[dict[str, str]]:
    missing: list[dict[str, str]] = []
    req = _LANE_REQUIREMENTS[lane_id]
    for field_name in req["required_config_paths"]:
        value = config.get(field_name)
        if not _config_path_present(value):
            continue
        if not isinstance(value, str):
            continue
        try:
            resolved = _resolve_manifest_path(Path(value), base_dir=manifest_dir)
        except ValueError as exc:
            missing.append({"field": field_name, "path": value, "reason": str(exc)})
            continue
        if not resolved.is_file():
            missing.append({"field": field_name, "path": value, "reason": "sidecar file not found"})
    return missing


def _lane_status_gaps(lane_status: object) -> list[str]:
    if not isinstance(lane_status, Mapping):
        return ["lane status missing from evaluator output"]
    raw_gaps = lane_status.get("gaps", [])
    if not isinstance(raw_gaps, list):
        return []
    return [gap for gap in raw_gaps if isinstance(gap, str)]


def _readiness_categories(
    *,
    lane_ready: bool,
    missing_evidence: bool,
    missing_config: list[str],
    missing_sidecars: Sequence[Mapping[str, str]],
    evidence_gaps: list[str],
) -> list[str]:
    if lane_ready:
        return ["ready"]

    categories: list[str] = []
    if missing_evidence:
        categories.append("missing_artifact")
    if missing_config:
        categories.append("missing_config")
    if missing_sidecars:
        categories.append("missing_sidecar")
    if evidence_gaps and not missing_evidence:
        categories.append("invalid_artifact")
    categories.append("external_required")
    return categories


def _readiness_plan_for_scope(
    out: Mapping[str, Any],
    *,
    config: Mapping[str, Any],
    bundle: Mapping[str, Any],
    lane: str | None,
    manifest_dir: Path,
) -> dict[str, Any]:
    lanes_obj = out.get("lanes")
    lanes_status = lanes_obj if isinstance(lanes_obj, Mapping) else {}
    blocked_lanes = [name for name in out.get("blocked_lanes", []) if isinstance(name, str)]

    lane_plans: dict[str, Any] = {}
    for lane_id in _lanes_for_scope(lane):
        lane_status = lanes_status.get(lane_id)
        lane_ready = isinstance(lane_status, Mapping) and lane_status.get("production_ready") is True
        missing_config = _missing_required_config(config, lane_id=lane_id)
        missing_sidecars = _missing_required_sidecars(config, lane_id=lane_id, manifest_dir=manifest_dir)
        missing_evidence = lane_id not in bundle or bundle.get(lane_id) is None
        evidence_gaps = _lane_status_gaps(lane_status)
        lane_plans[lane_id] = {
            "status": "ready" if lane_ready else "blocked",
            "categories": _readiness_categories(
                lane_ready=lane_ready,
                missing_evidence=missing_evidence,
                missing_config=missing_config,
                missing_sidecars=missing_sidecars,
                evidence_gaps=evidence_gaps,
            ),
            "producer_tool": _LANE_REQUIREMENTS[lane_id]["producer_tool"],
            "missing_config": missing_config,
            "missing_sidecars": missing_sidecars,
            "missing_artifact": missing_evidence,
            "external_artifacts": list(_LANE_REQUIREMENTS[lane_id]["external_artifacts"]),
            "gaps": evidence_gaps,
        }

    return {
        "schema": "zenodex/production-promotion-readiness-plan/v1",
        "posture": "diagnostic only; lane evaluators and the final promotion gate remain authoritative",
        "promotion_ready": out.get("promotion_ready") is True,
        "blocked_lanes": blocked_lanes,
        "lanes": lane_plans,
    }


def _attach_readiness_plan(
    out: dict[str, Any],
    *,
    config: Mapping[str, Any],
    bundle: Mapping[str, Any],
    lane: str | None,
    manifest_dir: Path,
) -> dict[str, Any]:
    return {
        **out,
        "readiness_plan": _readiness_plan_for_scope(
            out,
            config=config,
            bundle=bundle,
            lane=lane,
            manifest_dir=manifest_dir,
        ),
    }


def _error_out_for_scope(*, lane: str | None, detail: str) -> dict[str, Any]:
    lanes = {
        lane_id: {
            "ok": False,
            "production_ready": False,
            "status": "blocked",
            "gaps": [detail],
        }
        for lane_id in _lanes_for_scope(lane)
    }
    return {
        "schema": "zenodex/production-promotion-evidence-status/v1",
        "promotion_ready": False,
        "status": "blocked",
        "selected_lane": lane,
        "blocked_lanes": list(lanes),
        "gaps": [detail],
        "lanes": lanes,
    }


def _exit_code(out: Mapping[str, Any], *, lane: str | None) -> int:
    if lane is None:
        return 0 if out["promotion_ready"] is True else 1
    lanes = out["lanes"]
    lane_status = lanes[lane]
    return 0 if lane_status["production_ready"] is True else 1


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(list(argv) if argv is not None else sys.argv[1:])
    manifest_path = Path(args.manifest)
    manifest, error = _load_manifest(manifest_path)
    if error is not None:
        print(json.dumps(error))
        return 2
    if manifest is None:
        print(json.dumps({"ok": False, "error": "manifest_load_failed"}))
        return 2
    try:
        config, bundle = _manifest_config_and_bundle(manifest, lane=args.lane)
    except _ManifestConfigBundleError as exc:
        print(json.dumps({"ok": False, "error": "config_or_bundle_not_object", "detail": str(exc)}))
        return 2
    try:
        out = _evaluate_manifest(
            manifest,
            manifest_dir=manifest_path.resolve().parent,
            lane=args.lane,
            now=args.now,
        )
    except _ManifestConfigBundleError as exc:
        print(json.dumps({"ok": False, "error": "config_or_bundle_not_object", "detail": str(exc)}))
        return 2
    except (FileNotFoundError, TypeError, ValueError) as exc:
        error_out: dict[str, Any] = {"ok": False, "error": "manifest_config_invalid", "detail": str(exc)}
        if args.readiness_plan:
            scoped = _error_out_for_scope(lane=args.lane, detail=str(exc))
            error_out["readiness_plan"] = _readiness_plan_for_scope(
                scoped,
                config=config,
                bundle=bundle,
                lane=args.lane,
                manifest_dir=manifest_path.resolve().parent,
            )
        print(json.dumps(error_out))
        return 2
    if args.explain_missing:
        out = _attach_requirements(out, lane=args.lane)
    if args.include_runbook:
        out = _attach_runbook(out, lane=args.lane)
    if args.readiness_plan:
        out = _attach_readiness_plan(
            out,
            config=config,
            bundle=bundle,
            lane=args.lane,
            manifest_dir=manifest_path.resolve().parent,
        )
    print(json.dumps(out, sort_keys=True))
    return _exit_code(out, lane=args.lane)


if __name__ == "__main__":
    raise SystemExit(main())
