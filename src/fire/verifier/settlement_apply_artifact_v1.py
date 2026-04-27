from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

from src.fire.registry.bundle_v1 import verify_fire_registry_bundle
from src.fire.verifier.settlement_apply_report_v1 import verify_fire_settlement_apply_report


FIRE_SETTLEMENT_APPLY_ARTIFACT_RECEIPT_SCHEMA = "zenodex/fire-settlement-apply-artifact-receipt/v1"


def _canonical_json_bytes(payload: object) -> bytes:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def _payload_hash(payload: object) -> str:
    return "sha256:" + hashlib.sha256(_canonical_json_bytes(payload)).hexdigest()


def _sha256_path(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def _path_for_receipt(path: Path, *, base_dir: Path) -> str:
    resolved = path.resolve()
    if resolved.is_relative_to(base_dir):
        return resolved.relative_to(base_dir).as_posix()
    return str(resolved)


def build_fire_settlement_apply_artifact_receipt(
    report_path: str | Path,
    bundle_dir: str | Path,
) -> dict[str, object]:
    report_file = Path(report_path).resolve()
    bundle_root = Path(bundle_dir).resolve()
    payload = json.loads(report_file.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("apply report must be a JSON object")
    ok, err = verify_fire_settlement_apply_report(payload, expected_bundle_dir=bundle_root)
    if not ok:
        raise ValueError(f"apply report not accepted: {err or 'report_verification_failed'}")
    settlement_packet = payload.get("settlement_packet")
    apply_receipt = payload.get("apply_receipt")
    if not isinstance(settlement_packet, dict) or not isinstance(apply_receipt, dict):
        raise ValueError("apply report missing packet or apply receipt")

    normalized = {
        "schema": FIRE_SETTLEMENT_APPLY_ARTIFACT_RECEIPT_SCHEMA,
        "report_path": str(report_file),
        "report_file_sha256": _sha256_path(report_file),
        "report_hash": payload.get("report_hash"),
        "bundle_dir": str(bundle_root),
        "bundle_hash": payload.get("bundle_hash"),
        "object_hash": payload.get("object_hash"),
        "instance_hash": payload.get("instance_hash"),
        "cert_sha256": payload.get("cert_sha256"),
        "witness_hash": payload.get("witness_hash"),
        "settlement_packet_hash": settlement_packet.get("packet_hash"),
        "apply_receipt_hash": apply_receipt.get("receipt_hash"),
    }
    return {**normalized, "receipt_sha256": _payload_hash(normalized)}


def write_fire_settlement_apply_artifact_receipt(
    receipt_path: str | Path,
    report_path: str | Path,
    bundle_dir: str | Path,
) -> dict[str, object]:
    receipt_file = Path(receipt_path).resolve()
    receipt_file.parent.mkdir(parents=True, exist_ok=True)
    base_dir = receipt_file.parent.resolve()
    report_file = Path(report_path).resolve()
    bundle_root = Path(bundle_dir).resolve()

    receipt = build_fire_settlement_apply_artifact_receipt(report_file, bundle_root)
    stored = {
        **receipt,
        "report_path": _path_for_receipt(report_file, base_dir=base_dir),
        "bundle_dir": _path_for_receipt(bundle_root, base_dir=base_dir),
    }
    stored["receipt_sha256"] = _payload_hash({k: v for k, v in stored.items() if k != "receipt_sha256"})
    receipt_file.write_text(json.dumps(stored, sort_keys=True, indent=2), encoding="utf-8")
    return stored


def check_fire_settlement_apply_artifact_receipt(
    receipt_path: str | Path,
    *,
    expected_bundle_dir: str | Path | None = None,
    expected_bundle_hash: str | None = None,
    expected_object_hash: str | None = None,
    expected_instance_hash: str | None = None,
    expected_cert_sha256: str | None = None,
    expected_witness_hash: str | None = None,
    expected_report_hash: str | None = None,
) -> dict[str, Any]:
    receipt_file = Path(receipt_path).resolve()
    try:
        payload = json.loads(receipt_file.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return {"accepted": False, "violated_checks": ["parse_error"], "error": str(exc)}
    if not isinstance(payload, dict):
        return {"accepted": False, "violated_checks": ["schema_not_object"]}
    if payload.get("schema") != FIRE_SETTLEMENT_APPLY_ARTIFACT_RECEIPT_SCHEMA:
        return {"accepted": False, "violated_checks": ["schema_mismatch"]}

    violations: list[str] = []
    expected_hash = payload.get("receipt_sha256")
    observed_hash = _payload_hash({k: v for k, v in payload.items() if k != "receipt_sha256"})
    if expected_hash != observed_hash:
        violations.append("receipt_hash_mismatch")

    report_path = payload.get("report_path")
    bundle_dir = payload.get("bundle_dir")
    if not isinstance(report_path, str):
        violations.append("report_path_invalid")
    if not isinstance(bundle_dir, str):
        violations.append("bundle_dir_invalid")
    if violations:
        return {"accepted": False, "violated_checks": violations}

    report_file = Path(report_path)
    if not report_file.is_absolute():
        report_file = (receipt_file.parent / report_file).resolve()
    else:
        report_file = report_file.resolve()
    bundle_root = Path(bundle_dir)
    if not bundle_root.is_absolute():
        bundle_root = (receipt_file.parent / bundle_root).resolve()
    else:
        bundle_root = bundle_root.resolve()
    if not report_file.exists():
        violations.append("report_missing")
    if not bundle_root.exists():
        violations.append("bundle_dir_missing")
    if violations:
        return {"accepted": False, "violated_checks": violations}

    if payload.get("report_file_sha256") != _sha256_path(report_file):
        violations.append("report_file_sha256_mismatch")

    rebuilt = None
    if not violations:
        try:
            rebuilt = build_fire_settlement_apply_artifact_receipt(report_file, bundle_root)
            rebuilt = {
                **rebuilt,
                "report_path": _path_for_receipt(report_file, base_dir=receipt_file.parent.resolve()),
                "bundle_dir": _path_for_receipt(bundle_root, base_dir=receipt_file.parent.resolve()),
            }
            rebuilt["receipt_sha256"] = _payload_hash({k: v for k, v in rebuilt.items() if k != "receipt_sha256"})
        except ValueError as exc:
            violations.append(f"receipt_rebuild_error:{exc}")

    if rebuilt is not None:
        for field in (
            "report_hash",
            "bundle_hash",
            "object_hash",
            "instance_hash",
            "cert_sha256",
            "witness_hash",
            "settlement_packet_hash",
            "apply_receipt_hash",
            "report_path",
            "bundle_dir",
            "report_file_sha256",
            "receipt_sha256",
        ):
            if payload.get(field) != rebuilt.get(field):
                violations.append(f"{field}_mismatch")

    resolved_bundle_dir = str(bundle_root) if "bundle_root" in locals() else None
    derived_bundle_hash = None
    derived_object_hash = None
    derived_instance_hash = None
    derived_cert_sha256 = None
    if expected_bundle_dir is not None:
        expected_bundle_root = Path(expected_bundle_dir).resolve()
        if resolved_bundle_dir != str(expected_bundle_root):
            violations.append("expected_bundle_dir_mismatch")
        else:
            ok, err, bundle_manifest, object_manifest, object_instance, _object_lock = verify_fire_registry_bundle(
                expected_bundle_root
            )
            if not ok or bundle_manifest is None or object_manifest is None or object_instance is None:
                violations.append(f"expected_bundle_invalid:{err or 'unknown'}")
            else:
                derived_bundle_hash = bundle_manifest.bundle_hash
                derived_object_hash = object_manifest.manifest_hash
                derived_instance_hash = object_instance.instance_hash
                derived_cert_sha256 = bundle_manifest.certificate_file_sha256

    effective_expected_bundle_hash = expected_bundle_hash or derived_bundle_hash
    effective_expected_object_hash = expected_object_hash or derived_object_hash
    effective_expected_instance_hash = expected_instance_hash or derived_instance_hash
    effective_expected_cert_sha256 = expected_cert_sha256 or derived_cert_sha256
    if effective_expected_bundle_hash is not None and payload.get("bundle_hash") != effective_expected_bundle_hash:
        violations.append("expected_bundle_hash_mismatch")
    if effective_expected_object_hash is not None and payload.get("object_hash") != effective_expected_object_hash:
        violations.append("expected_object_hash_mismatch")
    if effective_expected_instance_hash is not None and payload.get("instance_hash") != effective_expected_instance_hash:
        violations.append("expected_instance_hash_mismatch")
    if effective_expected_cert_sha256 is not None and payload.get("cert_sha256") != effective_expected_cert_sha256:
        violations.append("expected_cert_sha256_mismatch")
    if expected_witness_hash is not None and payload.get("witness_hash") != expected_witness_hash:
        violations.append("expected_witness_hash_mismatch")
    if expected_report_hash is not None and payload.get("report_hash") != expected_report_hash:
        violations.append("expected_report_hash_mismatch")

    return {
        "accepted": not violations,
        "violated_checks": violations,
        "report_hash": payload.get("report_hash"),
        "bundle_hash": payload.get("bundle_hash"),
        "object_hash": payload.get("object_hash"),
        "instance_hash": payload.get("instance_hash"),
        "cert_sha256": payload.get("cert_sha256"),
        "witness_hash": payload.get("witness_hash"),
        "bundle_dir": resolved_bundle_dir,
    }


__all__ = [
    "FIRE_SETTLEMENT_APPLY_ARTIFACT_RECEIPT_SCHEMA",
    "build_fire_settlement_apply_artifact_receipt",
    "check_fire_settlement_apply_artifact_receipt",
    "write_fire_settlement_apply_artifact_receipt",
]
