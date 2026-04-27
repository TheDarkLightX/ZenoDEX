from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

from jsonschema import Draft202012Validator, FormatChecker

from src.fire.pathing_v1 import fire_acceptance_receipt_schema_path
from src.fire.verifier.object_package_v1 import (
    FireObjectPackageVerification,
    verify_fire_object_package,
)


FIRE_ACCEPTANCE_RECEIPT_SCHEMA = "zenodex/fire-acceptance-receipt/v1"
FIRE_ACCEPTANCE_RECEIPT_CHECK_REPORT_SCHEMA = "zenodex/fire-acceptance-receipt-check-report/v1"


def _canonical_json_bytes(payload: object) -> bytes:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def _sha256_bytes(payload: bytes) -> str:
    return "sha256:" + hashlib.sha256(payload).hexdigest()


def _sha256_file(path: Path) -> str:
    return _sha256_bytes(path.read_bytes())


def _receipt_hash(payload_without_hash: Mapping[str, object]) -> str:
    return _sha256_bytes(_canonical_json_bytes(dict(payload_without_hash)))


def _load_json(path: Path) -> Mapping[str, object]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise TypeError(f"{path} must contain a JSON object")
    return payload


def _error_path(error: Any) -> str:
    if not error.path:
        return "/"
    return "/" + "/".join(str(item) for item in error.path)


def _validate_against_schema(payload: Mapping[str, object]) -> tuple[bool, str | None]:
    schema = json.loads(fire_acceptance_receipt_schema_path().read_text(encoding="utf-8"))
    validator = Draft202012Validator(schema, format_checker=FormatChecker())
    errors = sorted(validator.iter_errors(payload), key=lambda item: tuple(item.path))
    if not errors:
        return True, None
    first = errors[0]
    return False, f"acceptance_receipt_schema_invalid:{_error_path(first)}:{first.message}"


def _strict_requirements_dict(
    *,
    require_replay_input: bool,
    require_compile_receipt: bool,
    require_kernel_receipt: bool,
    require_kernel_eval_receipt: bool,
    require_kernel_replay_receipt: bool,
    require_kernel_settlement_receipt: bool,
    require_proof_tree_cert: bool,
) -> dict[str, bool]:
    return {
        "replay_input": require_replay_input,
        "compile_receipt": require_compile_receipt,
        "kernel_receipt": require_kernel_receipt,
        "kernel_eval_receipt": require_kernel_eval_receipt,
        "kernel_replay_receipt": require_kernel_replay_receipt,
        "kernel_settlement_receipt": require_kernel_settlement_receipt,
        "proof_tree_certificate": require_proof_tree_cert,
    }


def _require_artifacts_for_strict_flags(
    verification: FireObjectPackageVerification,
    *,
    require_replay_input: bool,
    require_compile_receipt: bool,
    require_kernel_receipt: bool,
    require_kernel_eval_receipt: bool,
    require_kernel_replay_receipt: bool,
    require_kernel_settlement_receipt: bool,
    require_proof_tree_cert: bool,
) -> None:
    manifest = verification.bundle_manifest
    checks = (
        (require_replay_input, manifest.replay_input_path, manifest.replay_input_sha256, "replay_input"),
        (require_compile_receipt, manifest.compile_receipt_path, manifest.compile_receipt_sha256, "compile_receipt"),
        (require_kernel_receipt, manifest.kernel_receipt_path, manifest.kernel_receipt_sha256, "kernel_receipt"),
        (
            require_kernel_eval_receipt,
            manifest.kernel_eval_receipt_path,
            manifest.kernel_eval_receipt_sha256,
            "kernel_eval_receipt",
        ),
        (
            require_kernel_replay_receipt,
            manifest.kernel_replay_receipt_path,
            manifest.kernel_replay_receipt_sha256,
            "kernel_replay_receipt",
        ),
        (
            require_kernel_settlement_receipt,
            manifest.kernel_settlement_receipt_path,
            manifest.kernel_settlement_receipt_sha256,
            "kernel_settlement_receipt",
        ),
        (
            require_proof_tree_cert,
            manifest.proof_tree_certificate_path,
            manifest.proof_tree_certificate_sha256,
            "proof_tree_certificate",
        ),
    )
    for required, path, sha256, name in checks:
        if required and (path is None or sha256 is None):
            raise ValueError(f"{name}_missing")


def build_fire_acceptance_receipt(
    verification: FireObjectPackageVerification,
    *,
    require_replay_input: bool = False,
    require_compile_receipt: bool = False,
    require_kernel_receipt: bool = False,
    require_kernel_eval_receipt: bool = False,
    require_kernel_replay_receipt: bool = False,
    require_kernel_settlement_receipt: bool = False,
    require_proof_tree_cert: bool = False,
) -> dict[str, object]:
    _require_artifacts_for_strict_flags(
        verification,
        require_replay_input=require_replay_input,
        require_compile_receipt=require_compile_receipt,
        require_kernel_receipt=require_kernel_receipt,
        require_kernel_eval_receipt=require_kernel_eval_receipt,
        require_kernel_replay_receipt=require_kernel_replay_receipt,
        require_kernel_settlement_receipt=require_kernel_settlement_receipt,
        require_proof_tree_cert=require_proof_tree_cert,
    )
    bundle_dir = verification.bundle_dir
    bundle_manifest = verification.bundle_manifest
    bundle_manifest_path = bundle_dir / "bundle_manifest.json"
    artifacts = bundle_manifest.to_dict()["artifacts"]
    if not isinstance(artifacts, dict):
        raise TypeError("bundle manifest artifacts must be an object")

    payload: dict[str, object] = {
        "schema": FIRE_ACCEPTANCE_RECEIPT_SCHEMA,
        "object_name": verification.object_manifest.object_name,
        "object_version": verification.object_manifest.object_version,
        "object_family": verification.object_manifest.object_family,
        "bundle_hash": bundle_manifest.bundle_hash,
        "bundle_manifest_sha256": _sha256_file(bundle_manifest_path),
        "object_hash": verification.object_manifest.manifest_hash,
        "instance_hash": verification.object_instance.instance_hash,
        "lock_hash": verification.object_lock.lock_hash,
        "cert_sha256": verification.object_manifest.cert_sha256,
        "artifacts": artifacts,
        "strict_requirements": _strict_requirements_dict(
            require_replay_input=require_replay_input,
            require_compile_receipt=require_compile_receipt,
            require_kernel_receipt=require_kernel_receipt,
            require_kernel_eval_receipt=require_kernel_eval_receipt,
            require_kernel_replay_receipt=require_kernel_replay_receipt,
            require_kernel_settlement_receipt=require_kernel_settlement_receipt,
            require_proof_tree_cert=require_proof_tree_cert,
        ),
        "package_acceptance": {
            "ok": True,
            "accepted_gate": "FIREPackageGate",
            "artifact_schemas_valid": True,
            "instance_gates_ok": True,
            "certificate_instance_gate_claims_ok": True,
            "authorizes_settlement": False,
        },
    }
    return {**payload, "receipt_sha256": _receipt_hash(payload)}


@dataclass(frozen=True)
class FireAcceptanceReceiptVerification:
    receipt_path: Path | None
    schema_path: Path
    bundle_dir: Path
    receipt_file_sha256: str | None
    receipt_sha256: str
    bundle_hash: str
    bundle_manifest_sha256: str
    object_hash: str
    instance_hash: str
    cert_sha256: str

    def to_report_dict(self) -> dict[str, object]:
        return {
            "schema": FIRE_ACCEPTANCE_RECEIPT_CHECK_REPORT_SCHEMA,
            "ok": True,
            "receipt_path": None if self.receipt_path is None else str(self.receipt_path),
            "schema_path": str(self.schema_path),
            "bundle_dir": str(self.bundle_dir),
            "receipt_file_sha256": self.receipt_file_sha256,
            "receipt_sha256": self.receipt_sha256,
            "bundle_hash": self.bundle_hash,
            "bundle_manifest_sha256": self.bundle_manifest_sha256,
            "object_hash": self.object_hash,
            "instance_hash": self.instance_hash,
            "cert_sha256": self.cert_sha256,
            "authorizes_settlement": False,
        }


def verify_fire_acceptance_receipt(
    payload: Mapping[str, object],
    *,
    verification: FireObjectPackageVerification,
    require_replay_input: bool = False,
    require_compile_receipt: bool = False,
    require_kernel_receipt: bool = False,
    require_kernel_eval_receipt: bool = False,
    require_kernel_replay_receipt: bool = False,
    require_kernel_settlement_receipt: bool = False,
    require_proof_tree_cert: bool = False,
) -> tuple[bool, str | None, FireAcceptanceReceiptVerification | None]:
    schema_ok, schema_err = _validate_against_schema(payload)
    if not schema_ok:
        return False, schema_err, None

    observed_receipt_sha256 = payload.get("receipt_sha256")
    if not isinstance(observed_receipt_sha256, str):
        return False, "acceptance_receipt_hash_invalid", None
    expected_hash = _receipt_hash({key: value for key, value in payload.items() if key != "receipt_sha256"})
    if observed_receipt_sha256 != expected_hash:
        return False, "acceptance_receipt_hash_mismatch", None

    try:
        expected = build_fire_acceptance_receipt(
            verification,
            require_replay_input=require_replay_input,
            require_compile_receipt=require_compile_receipt,
            require_kernel_receipt=require_kernel_receipt,
            require_kernel_eval_receipt=require_kernel_eval_receipt,
            require_kernel_replay_receipt=require_kernel_replay_receipt,
            require_kernel_settlement_receipt=require_kernel_settlement_receipt,
            require_proof_tree_cert=require_proof_tree_cert,
        )
    except (OSError, TypeError, ValueError) as exc:
        return False, f"acceptance_receipt_rebuild_failed:{exc}", None

    if dict(payload) != expected:
        return False, "acceptance_receipt_mismatch", None

    return (
        True,
        None,
        FireAcceptanceReceiptVerification(
            receipt_path=None,
            schema_path=fire_acceptance_receipt_schema_path().resolve(),
            bundle_dir=verification.bundle_dir.resolve(),
            receipt_file_sha256=None,
            receipt_sha256=expected["receipt_sha256"],
            bundle_hash=expected["bundle_hash"],
            bundle_manifest_sha256=expected["bundle_manifest_sha256"],
            object_hash=expected["object_hash"],
            instance_hash=expected["instance_hash"],
            cert_sha256=expected["cert_sha256"],
        ),
    )


def build_fire_acceptance_receipt_for_bundle(
    bundle_dir: str | Path,
    *,
    expected_bundle_hash: str | None = None,
    expected_bundle_file_sha256: str | None = None,
    require_replay_input: bool = False,
    require_compile_receipt: bool = False,
    require_kernel_receipt: bool = False,
    require_kernel_eval_receipt: bool = False,
    require_kernel_replay_receipt: bool = False,
    require_kernel_settlement_receipt: bool = False,
    require_proof_tree_cert: bool = False,
) -> dict[str, object]:
    ok, err, verification = verify_fire_object_package(
        bundle_dir,
        expected_bundle_hash=expected_bundle_hash,
        expected_bundle_file_sha256=expected_bundle_file_sha256,
        require_replay_input=require_replay_input,
        require_compile_receipt=require_compile_receipt,
        require_kernel_receipt=require_kernel_receipt,
        require_kernel_eval_receipt=require_kernel_eval_receipt,
        require_kernel_replay_receipt=require_kernel_replay_receipt,
        require_kernel_settlement_receipt=require_kernel_settlement_receipt,
        require_proof_tree_cert=require_proof_tree_cert,
    )
    if not ok or verification is None:
        raise ValueError(err or "object_package_verification_failed")
    return build_fire_acceptance_receipt(
        verification,
        require_replay_input=require_replay_input,
        require_compile_receipt=require_compile_receipt,
        require_kernel_receipt=require_kernel_receipt,
        require_kernel_eval_receipt=require_kernel_eval_receipt,
        require_kernel_replay_receipt=require_kernel_replay_receipt,
        require_kernel_settlement_receipt=require_kernel_settlement_receipt,
        require_proof_tree_cert=require_proof_tree_cert,
    )


def write_fire_acceptance_receipt(
    path: str | Path,
    bundle_dir: str | Path,
    *,
    expected_bundle_hash: str | None = None,
    expected_bundle_file_sha256: str | None = None,
    require_replay_input: bool = False,
    require_compile_receipt: bool = False,
    require_kernel_receipt: bool = False,
    require_kernel_eval_receipt: bool = False,
    require_kernel_replay_receipt: bool = False,
    require_kernel_settlement_receipt: bool = False,
    require_proof_tree_cert: bool = False,
) -> dict[str, object]:
    receipt_path = Path(path)
    receipt_path.parent.mkdir(parents=True, exist_ok=True)
    receipt = build_fire_acceptance_receipt_for_bundle(
        bundle_dir,
        expected_bundle_hash=expected_bundle_hash,
        expected_bundle_file_sha256=expected_bundle_file_sha256,
        require_replay_input=require_replay_input,
        require_compile_receipt=require_compile_receipt,
        require_kernel_receipt=require_kernel_receipt,
        require_kernel_eval_receipt=require_kernel_eval_receipt,
        require_kernel_replay_receipt=require_kernel_replay_receipt,
        require_kernel_settlement_receipt=require_kernel_settlement_receipt,
        require_proof_tree_cert=require_proof_tree_cert,
    )
    receipt_path.write_text(json.dumps(receipt, sort_keys=True, indent=2), encoding="utf-8")
    return receipt


def verify_fire_acceptance_receipt_file(
    path: str | Path,
    *,
    bundle_dir: str | Path,
    expected_receipt_file_sha256: str | None = None,
    expected_bundle_hash: str | None = None,
    expected_bundle_file_sha256: str | None = None,
    require_replay_input: bool = False,
    require_compile_receipt: bool = False,
    require_kernel_receipt: bool = False,
    require_kernel_eval_receipt: bool = False,
    require_kernel_replay_receipt: bool = False,
    require_kernel_settlement_receipt: bool = False,
    require_proof_tree_cert: bool = False,
) -> tuple[bool, str | None, FireAcceptanceReceiptVerification | None]:
    receipt_path = Path(path).resolve()
    bundle_root = Path(bundle_dir).resolve()
    try:
        payload = _load_json(receipt_path)
        receipt_file_sha256 = _sha256_file(receipt_path)
    except (OSError, TypeError, json.JSONDecodeError) as exc:
        return False, f"acceptance_receipt_parse_error:{exc}", None

    if expected_receipt_file_sha256 is not None and receipt_file_sha256 != expected_receipt_file_sha256:
        return False, "expected_receipt_file_sha256_mismatch", None

    ok, err, package_verification = verify_fire_object_package(
        bundle_root,
        expected_bundle_hash=expected_bundle_hash,
        expected_bundle_file_sha256=expected_bundle_file_sha256,
        require_replay_input=require_replay_input,
        require_compile_receipt=require_compile_receipt,
        require_kernel_receipt=require_kernel_receipt,
        require_kernel_eval_receipt=require_kernel_eval_receipt,
        require_kernel_replay_receipt=require_kernel_replay_receipt,
        require_kernel_settlement_receipt=require_kernel_settlement_receipt,
        require_proof_tree_cert=require_proof_tree_cert,
    )
    if not ok or package_verification is None:
        return False, f"object_package_invalid:{err or 'object_package_verification_failed'}", None

    receipt_ok, receipt_err, verification = verify_fire_acceptance_receipt(
        payload,
        verification=package_verification,
        require_replay_input=require_replay_input,
        require_compile_receipt=require_compile_receipt,
        require_kernel_receipt=require_kernel_receipt,
        require_kernel_eval_receipt=require_kernel_eval_receipt,
        require_kernel_replay_receipt=require_kernel_replay_receipt,
        require_kernel_settlement_receipt=require_kernel_settlement_receipt,
        require_proof_tree_cert=require_proof_tree_cert,
    )
    if not receipt_ok or verification is None:
        return False, receipt_err or "acceptance_receipt_verification_failed", None

    return (
        True,
        None,
        FireAcceptanceReceiptVerification(
            receipt_path=receipt_path,
            schema_path=verification.schema_path,
            bundle_dir=bundle_root,
            receipt_file_sha256=receipt_file_sha256,
            receipt_sha256=verification.receipt_sha256,
            bundle_hash=verification.bundle_hash,
            bundle_manifest_sha256=verification.bundle_manifest_sha256,
            object_hash=verification.object_hash,
            instance_hash=verification.instance_hash,
            cert_sha256=verification.cert_sha256,
        ),
    )


__all__ = [
    "FIRE_ACCEPTANCE_RECEIPT_SCHEMA",
    "FIRE_ACCEPTANCE_RECEIPT_CHECK_REPORT_SCHEMA",
    "FireAcceptanceReceiptVerification",
    "build_fire_acceptance_receipt",
    "build_fire_acceptance_receipt_for_bundle",
    "verify_fire_acceptance_receipt",
    "verify_fire_acceptance_receipt_file",
    "write_fire_acceptance_receipt",
]
