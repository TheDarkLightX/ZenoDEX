from __future__ import annotations

from pathlib import Path
from typing import Any, Mapping

from src.fire.registry.bundle_v1 import verify_fire_registry_bundle
from src.fire.verifier.settlement_v1 import (
    FIRE_SETTLEMENT_AUTHORITY_COMMAND_TAG,
    FireVerifierReceipt,
    fire_witness_binding_hash,
    verify_fire_settlement_authority_receipt,
)


def _require_int(name: str, value: object) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def validate_persisted_bundle_command_args(
    *,
    state: Mapping[str, Any],
    args: Mapping[str, Any],
    expected_ir_hash: str,
) -> str | None:
    persisted_bundle_dir = args.get("persisted_bundle_dir")
    if persisted_bundle_dir is not None:
        if not isinstance(persisted_bundle_dir, str) or not persisted_bundle_dir:
            return "persisted bundle dir must be a non-empty string"
        ok, err, _bundle_manifest, object_manifest, _bundle_instance, _bundle_lock = verify_fire_registry_bundle(
            Path(persisted_bundle_dir),
            expected_bundle_hash=args.get("expected_bundle_hash"),
            expected_bundle_file_sha256=args.get("expected_bundle_file_sha256"),
        )
        if not ok or object_manifest is None:
            return f"persisted bundle invalid: {err or 'unknown'}"
        if object_manifest.ir_hash != expected_ir_hash:
            return "persisted bundle ir_hash mismatch"
        expected_cert_sha256 = args.get("expected_cert_sha256")
        if expected_cert_sha256 is not None and object_manifest.cert_sha256 != expected_cert_sha256:
            return "persisted bundle cert hash mismatch"
        try:
            artifact_lower = _require_int("state.artifact_lower", state.get("artifact_lower"))
            artifact_upper = _require_int("state.artifact_upper", state.get("artifact_upper"))
        except TypeError as exc:
            return f"state artifact bounds invalid: {exc}"
        if object_manifest.artifact_lower != artifact_lower or object_manifest.artifact_upper != artifact_upper:
            return "persisted bundle artifact bound mismatch"
        return None
    return None


def validate_persisted_bundle_settlement_receipt(
    *,
    state_after: Mapping[str, Any],
    args: Mapping[str, Any],
    expected_ir_hash: str,
    command_tag: str = FIRE_SETTLEMENT_AUTHORITY_COMMAND_TAG,
    witness_inputs: Mapping[str, object] | None = None,
) -> str | None:
    persisted_bundle_dir = args.get("persisted_bundle_dir")
    if persisted_bundle_dir is None:
        if command_tag == "firev_accept_and_settle":
            return "persisted bundle dir missing"
        return None
    if not isinstance(persisted_bundle_dir, str) or not persisted_bundle_dir:
        return "persisted bundle dir must be a non-empty string"
    ok, err, bundle_manifest, object_manifest, bundle_instance, _bundle_lock = verify_fire_registry_bundle(
        Path(persisted_bundle_dir),
        expected_bundle_hash=args.get("expected_bundle_hash"),
        expected_bundle_file_sha256=args.get("expected_bundle_file_sha256"),
    )
    if not ok or bundle_manifest is None or object_manifest is None or bundle_instance is None:
        return f"persisted bundle invalid: {err or 'unknown'}"
    if object_manifest.ir_hash != expected_ir_hash:
        return "persisted bundle ir_hash mismatch"
    receipt_payload = args.get("verifier_receipt")
    if not isinstance(receipt_payload, Mapping):
        return "verifier receipt missing"
    try:
        receipt = FireVerifierReceipt.from_dict(receipt_payload)
    except (TypeError, ValueError, KeyError) as exc:
        return f"verifier receipt invalid: {exc}"
    try:
        expected_witness_hash = None if witness_inputs is None else fire_witness_binding_hash(witness_inputs)
    except (TypeError, ValueError) as exc:
        return f"witness binding invalid: {exc}"
    try:
        expected_holder_delta = _require_int("state_after.holder_delta", state_after.get("holder_delta"))
        expected_writer_delta = _require_int("state_after.writer_delta", state_after.get("writer_delta"))
    except TypeError as exc:
        return f"state delta invalid: {exc}"
    ok, err = verify_fire_settlement_authority_receipt(
        receipt,
        expected_object_hash=object_manifest.manifest_hash,
        expected_instance_hash=bundle_instance.instance_hash,
        expected_cert_sha256=object_manifest.cert_sha256,
        expected_holder_delta=expected_holder_delta,
        expected_writer_delta=expected_writer_delta,
        expected_command_tag=command_tag,
        expected_bundle_hash=bundle_manifest.bundle_hash,
        expected_witness_hash=expected_witness_hash,
    )
    if not ok:
        return f"verifier receipt invalid: {err or 'unknown'}"
    return None


__all__ = [
    "validate_persisted_bundle_command_args",
    "validate_persisted_bundle_settlement_receipt",
]
