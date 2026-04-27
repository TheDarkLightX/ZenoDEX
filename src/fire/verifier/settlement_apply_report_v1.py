from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any, Mapping

from src.fire.kernel.apply_receipt_v1 import FireApplyReceipt, verify_fire_authority_apply_receipt
from src.fire.registry.bundle_v1 import load_fire_registry_bundle, verify_fire_registry_bundle
from src.fire.verifier.settlement_v1 import (
    FIRE_SETTLEMENT_AUTHORITY_COMMAND_TAG,
    FireSettlementPacket,
    verify_fire_settlement_authority_packet,
)


FIRE_SETTLEMENT_APPLY_REPORT_SCHEMA = "zenodex/fire-settlement-apply-report/v1"


def _canonical_json_bytes(payload: Mapping[str, object]) -> bytes:
    return json.dumps(dict(payload), sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def _sha256_bytes(payload: bytes) -> str:
    return "sha256:" + hashlib.sha256(payload).hexdigest()


def settlement_apply_report_payload_without_hash(payload: Mapping[str, Any]) -> dict[str, object]:
    return {str(key): value for key, value in payload.items() if key != "report_hash"}


def fire_settlement_apply_report_hash(payload_without_hash: Mapping[str, object]) -> str:
    return _sha256_bytes(_canonical_json_bytes(payload_without_hash))


def build_fire_settlement_apply_report(payload_without_hash: Mapping[str, object]) -> dict[str, object]:
    report = dict(payload_without_hash)
    report["report_hash"] = fire_settlement_apply_report_hash(report)
    return report


def verify_fire_settlement_apply_report(
    payload: Mapping[str, Any],
    *,
    expected_object_hash: str | None = None,
    expected_instance_hash: str | None = None,
    expected_cert_sha256: str | None = None,
    expected_bundle_hash: str | None = None,
    expected_witness_hash: str | None = None,
    expected_bundle_dir: str | Path | None = None,
    expected_command_tag: str = FIRE_SETTLEMENT_AUTHORITY_COMMAND_TAG,
) -> tuple[bool, str | None]:
    if not isinstance(payload, Mapping):
        raise TypeError("payload must be a mapping")
    if payload.get("schema") != FIRE_SETTLEMENT_APPLY_REPORT_SCHEMA:
        return False, "schema_mismatch"
    if payload.get("ok") is not True:
        return False, "ok_false"
    if payload.get("report_hash") != fire_settlement_apply_report_hash(settlement_apply_report_payload_without_hash(payload)):
        return False, "report_hash_mismatch"

    try:
        packet = FireSettlementPacket.from_dict(payload.get("settlement_packet"))
    except (TypeError, ValueError, KeyError) as exc:
        return False, f"settlement_packet_invalid:{exc}"
    ok, err = verify_fire_settlement_authority_packet(
        packet,
        expected_object_hash=expected_object_hash,
        expected_instance_hash=expected_instance_hash,
        expected_cert_sha256=expected_cert_sha256,
        expected_bundle_hash=expected_bundle_hash,
        expected_witness_hash=expected_witness_hash,
        expected_command_tag=expected_command_tag,
    )
    if not ok:
        return False, f"settlement_packet_{err or 'invalid'}"

    try:
        apply_receipt = FireApplyReceipt.from_dict(payload.get("apply_receipt"))
    except (TypeError, ValueError, KeyError) as exc:
        return False, f"apply_receipt_invalid:{exc}"
    ok, err = verify_fire_authority_apply_receipt(
        apply_receipt,
        packet=packet,
        expected_object_hash=expected_object_hash,
        expected_instance_hash=expected_instance_hash,
        expected_cert_sha256=expected_cert_sha256,
        expected_bundle_hash=expected_bundle_hash,
        expected_witness_hash=expected_witness_hash,
        expected_command_tag=expected_command_tag,
    )
    if not ok:
        return False, f"apply_receipt_{err or 'invalid'}"

    receipt = packet.receipt
    if payload.get("verifier_receipt") != receipt.to_dict():
        return False, "verifier_receipt_mismatch"
    if payload.get("object_hash") != receipt.object_hash:
        return False, "object_hash_mismatch"
    if payload.get("instance_hash") != receipt.instance_hash:
        return False, "instance_hash_mismatch"
    if payload.get("cert_sha256") != receipt.cert_sha256:
        return False, "cert_sha256_mismatch"
    if payload.get("bundle_hash") != receipt.bundle_hash:
        return False, "bundle_hash_mismatch"
    if payload.get("witness_hash") != receipt.witness_hash:
        return False, "witness_hash_mismatch"
    if payload.get("holder_delta") != packet.holder_delta:
        return False, "holder_delta_mismatch"
    if payload.get("writer_delta") != packet.writer_delta:
        return False, "writer_delta_mismatch"
    if payload.get("payoff_out") != packet.payoff_out:
        return False, "payoff_out_mismatch"
    if payload.get("holder_balance_before") != apply_receipt.holder_balance_before:
        return False, "holder_balance_before_mismatch"
    if payload.get("writer_balance_before") != apply_receipt.writer_balance_before:
        return False, "writer_balance_before_mismatch"
    if payload.get("holder_balance_after") != apply_receipt.holder_balance_after:
        return False, "holder_balance_after_mismatch"
    if payload.get("writer_balance_after") != apply_receipt.writer_balance_after:
        return False, "writer_balance_after_mismatch"

    if expected_bundle_dir is not None:
        bundle_dir = Path(expected_bundle_dir)
        ok, err, bundle_manifest, object_manifest, object_instance, _object_lock = verify_fire_registry_bundle(
            bundle_dir,
            expected_bundle_hash=receipt.bundle_hash,
        )
        if not ok or bundle_manifest is None or object_manifest is None or object_instance is None:
            return False, f"bundle_{err or 'invalid'}"
        _bundle_manifest, bundle_file_sha256, _object_manifest, _object_instance, _object_lock = load_fire_registry_bundle(
            bundle_dir
        )
        if payload.get("bundle_dir") != str(bundle_dir.resolve()):
            return False, "bundle_dir_mismatch"
        if payload.get("bundle_file_sha256") != bundle_file_sha256:
            return False, "bundle_file_sha256_mismatch"
        if payload.get("object_name") != object_manifest.object_name:
            return False, "object_name_mismatch"
        if payload.get("object_version") != object_manifest.object_version:
            return False, "object_version_mismatch"
        if payload.get("object_family") != object_manifest.object_family:
            return False, "object_family_mismatch"
        if payload.get("object_hash") != object_manifest.manifest_hash:
            return False, "bundle_object_hash_mismatch"
        if payload.get("instance_hash") != object_instance.instance_hash:
            return False, "bundle_instance_hash_mismatch"
        if payload.get("cert_sha256") != object_manifest.cert_sha256:
            return False, "bundle_cert_sha256_mismatch"

    return True, None


__all__ = [
    "FIRE_SETTLEMENT_APPLY_REPORT_SCHEMA",
    "build_fire_settlement_apply_report",
    "fire_settlement_apply_report_hash",
    "settlement_apply_report_payload_without_hash",
    "verify_fire_settlement_apply_report",
]
