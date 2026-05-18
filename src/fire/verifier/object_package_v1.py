from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

from jsonschema import Draft202012Validator, FormatChecker

from src.fire.pathing_v1 import (
    fire_cert_schema_path,
    fire_cert_rules_schema_path,
    fire_compile_receipt_schema_path,
    fire_instance_schema_path,
    fire_ir_schema_path,
    fire_kernel_eval_receipt_schema_path,
    fire_kernel_replay_receipt_schema_path,
    fire_kernel_receipt_schema_path,
    fire_kernel_settlement_receipt_schema_path,
    fire_lock_schema_path,
    fire_object_package_schema_path,
    fire_replay_input_schema_path,
)
from src.fire.compiler.compile_receipt_v1 import verify_fire_compile_receipt
from src.fire.kernel.kernel_eval_receipt_v1 import verify_fire_kernel_eval_receipt
from src.fire.kernel.kernel_replay_receipt_v1 import verify_fire_kernel_replay_receipt
from src.fire.kernel.kernel_receipt_v1 import verify_fire_kernel_receipt
from src.fire.kernel.kernel_settlement_receipt_v1 import verify_fire_kernel_settlement_receipt
from src.fire.registry.bundle_v1 import (
    FireObjectDependencyLock,
    FireObjectInstanceManifest,
    FireObjectManifest,
    FireRegistryBundleManifest,
    verify_fire_registry_bundle,
)
from src.fire.registry.instance_v1 import FireInstanceGateReport, verify_fire_object_instance_against_manifest
from src.fire.registry.object_manifest_v1 import expected_fire_instance_gate_claims
from src.fire.registry.replay_input_v1 import FireReplayInput, verify_fire_replay_input
from src.fire.verifier.cert_v1 import FireIntervalCertificate
from src.fire.verifier.proof_tree_cert_v1 import (
    expected_fire_proof_tree_authorization_summary,
    expected_fire_proof_tree_claim_evidence,
    expected_fire_proof_tree_contract_receipt_summary,
    expected_fire_proof_tree_dependency_summary,
    expected_fire_proof_tree_dependency_hashes,
    expected_fire_proof_tree_integer_eval_summary,
    expected_fire_proof_tree_instance_bind_summary,
    expected_fire_proof_tree_maturity_summary,
    expected_fire_proof_tree_nonce_summary,
    expected_fire_proof_tree_object_bind_summary,
    expected_fire_proof_tree_param_summary,
    expected_fire_proof_tree_replay_summary,
    expected_fire_proof_tree_unit_summary,
    expected_fire_proof_tree_window_summary,
    expected_fire_proof_tree_witness_policy_summary,
    summarize_fire_interval_certificate,
    verify_fire_proof_tree_certificate,
)


OBJECT_PACKAGE_CHECK_REPORT_SCHEMA = "zenodex/fire-object-package-check-report/v1"


def _load_json(path: Path) -> Mapping[str, object]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise TypeError(f"{path} must contain a JSON object")
    return payload


def _error_path(error: Any) -> str:
    if not error.path:
        return "/"
    return "/" + "/".join(str(item) for item in error.path)


def _validate_against_schema(
    payload: Mapping[str, object],
    *,
    schema_path: Path,
    artifact_name: str,
) -> tuple[bool, str | None]:
    schema = json.loads(schema_path.read_text(encoding="utf-8"))
    validator = Draft202012Validator(schema, format_checker=FormatChecker())
    errors = sorted(validator.iter_errors(payload), key=lambda item: tuple(item.path))
    if not errors:
        return True, None
    first = errors[0]
    return False, f"{artifact_name}_schema_invalid:{_error_path(first)}:{first.message}"


@dataclass(frozen=True)
class FireObjectPackageSchemaFiles:
    object_manifest_schema: Path
    object_instance_schema: Path
    object_lock_schema: Path
    certificate_schema: Path
    compile_receipt_schema: Path
    kernel_receipt_schema: Path
    kernel_eval_receipt_schema: Path
    kernel_replay_receipt_schema: Path
    kernel_settlement_receipt_schema: Path
    proof_tree_certificate_schema: Path
    replay_input_schema: Path
    object_package_schema: Path

    def to_dict(self) -> dict[str, str]:
        return {
            "object_manifest_schema": str(self.object_manifest_schema.resolve()),
            "object_instance_schema": str(self.object_instance_schema.resolve()),
            "object_lock_schema": str(self.object_lock_schema.resolve()),
            "certificate_schema": str(self.certificate_schema.resolve()),
            "compile_receipt_schema": str(self.compile_receipt_schema.resolve()),
            "kernel_receipt_schema": str(self.kernel_receipt_schema.resolve()),
            "kernel_eval_receipt_schema": str(self.kernel_eval_receipt_schema.resolve()),
            "kernel_replay_receipt_schema": str(self.kernel_replay_receipt_schema.resolve()),
            "kernel_settlement_receipt_schema": str(self.kernel_settlement_receipt_schema.resolve()),
            "proof_tree_certificate_schema": str(self.proof_tree_certificate_schema.resolve()),
            "replay_input_schema": str(self.replay_input_schema.resolve()),
            "object_package_schema": str(self.object_package_schema.resolve()),
        }


@dataclass(frozen=True)
class FireObjectPackageVerification:
    bundle_dir: Path
    bundle_manifest: FireRegistryBundleManifest
    object_manifest: FireObjectManifest
    object_instance: FireObjectInstanceManifest
    object_lock: FireObjectDependencyLock
    certificate: FireIntervalCertificate
    instance_gate_report: FireInstanceGateReport
    schema_files: FireObjectPackageSchemaFiles

    def to_report_dict(self) -> dict[str, object]:
        return {
            "schema": OBJECT_PACKAGE_CHECK_REPORT_SCHEMA,
            "ok": True,
            "bundle_dir": str(self.bundle_dir.resolve()),
            "bundle_hash": self.bundle_manifest.bundle_hash,
            "object_name": self.object_manifest.object_name,
            "object_version": self.object_manifest.object_version,
            "object_family": self.object_manifest.object_family,
            "object_hash": self.object_manifest.manifest_hash,
            "instance_hash": self.object_instance.instance_hash,
            "lock_hash": self.object_lock.lock_hash,
            "cert_sha256": self.object_manifest.cert_sha256,
            "artifact_schemas_valid": True,
            "compile_receipt_present": self.bundle_manifest.compile_receipt_path is not None,
            "kernel_receipt_present": self.bundle_manifest.kernel_receipt_path is not None,
            "kernel_eval_receipt_present": self.bundle_manifest.kernel_eval_receipt_path is not None,
            "kernel_replay_receipt_present": self.bundle_manifest.kernel_replay_receipt_path is not None,
            "kernel_settlement_receipt_present": self.bundle_manifest.kernel_settlement_receipt_path is not None,
            "proof_tree_cert_present": self.bundle_manifest.proof_tree_certificate_path is not None,
            "replay_input_present": self.bundle_manifest.replay_input_path is not None,
            "schema_files": self.schema_files.to_dict(),
            "certificate_instance_gate_claims": (
                None
                if self.certificate.instance_gate_claims is None
                else self.certificate.instance_gate_claims.to_dict()
            ),
            "expected_certificate_instance_gate_claims": expected_fire_instance_gate_claims(self.object_manifest).to_dict(),
            "instance_gates": self.instance_gate_report.to_dict(),
        }


def fire_object_package_schema_files() -> FireObjectPackageSchemaFiles:
    return FireObjectPackageSchemaFiles(
        object_manifest_schema=fire_ir_schema_path(),
        object_instance_schema=fire_instance_schema_path(),
        object_lock_schema=fire_lock_schema_path(),
        certificate_schema=fire_cert_schema_path(),
        compile_receipt_schema=fire_compile_receipt_schema_path(),
        kernel_receipt_schema=fire_kernel_receipt_schema_path(),
        kernel_eval_receipt_schema=fire_kernel_eval_receipt_schema_path(),
        kernel_replay_receipt_schema=fire_kernel_replay_receipt_schema_path(),
        kernel_settlement_receipt_schema=fire_kernel_settlement_receipt_schema_path(),
        proof_tree_certificate_schema=fire_cert_rules_schema_path(),
        replay_input_schema=fire_replay_input_schema_path(),
        object_package_schema=fire_object_package_schema_path(),
    )


def verify_fire_object_package(
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
) -> tuple[bool, str | None, FireObjectPackageVerification | None]:
    ok, err, bundle_manifest, object_manifest, object_instance, object_lock = verify_fire_registry_bundle(
        bundle_dir,
        expected_bundle_hash=expected_bundle_hash,
        expected_bundle_file_sha256=expected_bundle_file_sha256,
    )
    if not ok or bundle_manifest is None or object_manifest is None or object_instance is None or object_lock is None:
        return False, err or "object_package_verification_failed", None

    root = Path(bundle_dir)
    schema_files = fire_object_package_schema_files()
    raw_bundle_manifest = _load_json(root / "bundle_manifest.json")
    raw_object_manifest = _load_json(root / bundle_manifest.object_manifest_path)
    raw_object_instance = _load_json(root / bundle_manifest.object_instance_path)
    raw_object_lock = _load_json(root / bundle_manifest.object_lock_path)
    raw_certificate = _load_json(root / bundle_manifest.certificate_path)
    raw_compile_receipt = None
    if bundle_manifest.compile_receipt_path is not None:
        raw_compile_receipt = _load_json(root / bundle_manifest.compile_receipt_path)
    elif require_compile_receipt:
        return False, "compile_receipt_missing", None
    raw_kernel_receipt = None
    if bundle_manifest.kernel_receipt_path is not None:
        raw_kernel_receipt = _load_json(root / bundle_manifest.kernel_receipt_path)
    elif require_kernel_receipt:
        return False, "kernel_receipt_missing", None
    raw_kernel_eval_receipt = None
    if bundle_manifest.kernel_eval_receipt_path is not None:
        raw_kernel_eval_receipt = _load_json(root / bundle_manifest.kernel_eval_receipt_path)
    elif require_kernel_eval_receipt:
        return False, "kernel_eval_receipt_missing", None
    raw_kernel_settlement_receipt = None
    if bundle_manifest.kernel_settlement_receipt_path is not None:
        raw_kernel_settlement_receipt = _load_json(root / bundle_manifest.kernel_settlement_receipt_path)
    elif require_kernel_settlement_receipt:
        return False, "kernel_settlement_receipt_missing", None
    raw_kernel_replay_receipt = None
    if bundle_manifest.kernel_replay_receipt_path is not None:
        raw_kernel_replay_receipt = _load_json(root / bundle_manifest.kernel_replay_receipt_path)
    elif require_kernel_replay_receipt:
        return False, "kernel_replay_receipt_missing", None
    raw_proof_tree_cert = None
    if bundle_manifest.proof_tree_certificate_path is not None:
        raw_proof_tree_cert = _load_json(root / bundle_manifest.proof_tree_certificate_path)
    elif require_proof_tree_cert:
        return False, "proof_tree_certificate_missing", None
    raw_replay_input = None
    if bundle_manifest.replay_input_path is not None:
        raw_replay_input = _load_json(root / bundle_manifest.replay_input_path)
    elif require_replay_input:
        return False, "replay_input_missing", None

    validations = (
        ("object_package", raw_bundle_manifest, schema_files.object_package_schema),
        ("object_manifest", raw_object_manifest, schema_files.object_manifest_schema),
        ("object_instance", raw_object_instance, schema_files.object_instance_schema),
        ("object_lock", raw_object_lock, schema_files.object_lock_schema),
        ("certificate", raw_certificate, schema_files.certificate_schema),
    )
    for artifact_name, payload, schema_path in validations:
        valid, schema_err = _validate_against_schema(payload, schema_path=schema_path, artifact_name=artifact_name)
        if not valid:
            return False, schema_err, None
    if raw_proof_tree_cert is not None:
        valid, schema_err = _validate_against_schema(
            raw_proof_tree_cert,
            schema_path=schema_files.proof_tree_certificate_schema,
            artifact_name="proof_tree_certificate",
        )
        if not valid:
            return False, schema_err, None
    if raw_compile_receipt is not None:
        valid, schema_err = _validate_against_schema(
            raw_compile_receipt,
            schema_path=schema_files.compile_receipt_schema,
            artifact_name="compile_receipt",
        )
        if not valid:
            return False, schema_err, None
    if raw_kernel_receipt is not None:
        valid, schema_err = _validate_against_schema(
            raw_kernel_receipt,
            schema_path=schema_files.kernel_receipt_schema,
            artifact_name="kernel_receipt",
        )
        if not valid:
            return False, schema_err, None
    if raw_kernel_eval_receipt is not None:
        valid, schema_err = _validate_against_schema(
            raw_kernel_eval_receipt,
            schema_path=schema_files.kernel_eval_receipt_schema,
            artifact_name="kernel_eval_receipt",
        )
        if not valid:
            return False, schema_err, None
    if raw_kernel_settlement_receipt is not None:
        valid, schema_err = _validate_against_schema(
            raw_kernel_settlement_receipt,
            schema_path=schema_files.kernel_settlement_receipt_schema,
            artifact_name="kernel_settlement_receipt",
        )
        if not valid:
            return False, schema_err, None
    if raw_kernel_replay_receipt is not None:
        valid, schema_err = _validate_against_schema(
            raw_kernel_replay_receipt,
            schema_path=schema_files.kernel_replay_receipt_schema,
            artifact_name="kernel_replay_receipt",
        )
        if not valid:
            return False, schema_err, None
    if raw_replay_input is not None:
        valid, schema_err = _validate_against_schema(
            raw_replay_input,
            schema_path=schema_files.replay_input_schema,
            artifact_name="replay_input",
        )
        if not valid:
            return False, schema_err, None

    certificate = FireIntervalCertificate.from_dict(raw_certificate)
    gate_ok, gate_err, gate_report = verify_fire_object_instance_against_manifest(
        object_instance,
        object_manifest=object_manifest,
    )
    if not gate_ok:
        return False, gate_err or "object_instance_gate_invalid", None

    claims = certificate.instance_gate_claims
    expected_claims = expected_fire_instance_gate_claims(object_manifest)
    if claims is None:
        return False, "certificate_instance_gate_claims_missing", None
    if claims != expected_claims:
        return False, "certificate_instance_gate_claims_mismatch", None
    if raw_compile_receipt is not None:
        compile_ok, compile_err, _compile_verification = verify_fire_compile_receipt(
            raw_compile_receipt,
            object_manifest=object_manifest,
            object_instance=object_instance,
        )
        if not compile_ok:
            return False, compile_err or "compile_receipt_invalid", None
    if raw_kernel_receipt is not None:
        kernel_ok, kernel_err, _kernel_verification = verify_fire_kernel_receipt(
            raw_kernel_receipt,
            object_manifest=object_manifest,
            object_instance=object_instance,
        )
        if not kernel_ok:
            return False, kernel_err or "kernel_receipt_invalid", None
    if raw_kernel_eval_receipt is not None:
        kernel_eval_ok, kernel_eval_err, _kernel_eval_verification = verify_fire_kernel_eval_receipt(
            raw_kernel_eval_receipt,
            object_manifest=object_manifest,
            object_instance=object_instance,
            expected_kernel_receipt_sha256=bundle_manifest.kernel_receipt_sha256,
        )
        if not kernel_eval_ok:
            return False, kernel_eval_err or "kernel_eval_receipt_invalid", None
    if raw_kernel_settlement_receipt is not None:
        if raw_replay_input is None or bundle_manifest.replay_input_sha256 is None:
            return False, "kernel_settlement_receipt_requires_replay_input", None
        if bundle_manifest.kernel_receipt_sha256 is None:
            return False, "kernel_settlement_receipt_requires_kernel_receipt", None
        if bundle_manifest.kernel_eval_receipt_sha256 is None:
            return False, "kernel_settlement_receipt_requires_kernel_eval_receipt", None
        kernel_settlement_ok, kernel_settlement_err, _kernel_settlement_verification = verify_fire_kernel_settlement_receipt(
            raw_kernel_settlement_receipt,
            object_manifest=object_manifest,
            object_instance=object_instance,
            replay_input=FireReplayInput.from_dict(raw_replay_input),
            expected_replay_input_sha256=bundle_manifest.replay_input_sha256,
            expected_kernel_receipt_sha256=bundle_manifest.kernel_receipt_sha256,
            expected_kernel_eval_receipt_sha256=bundle_manifest.kernel_eval_receipt_sha256,
        )
        if not kernel_settlement_ok:
            return False, kernel_settlement_err or "kernel_settlement_receipt_invalid", None
    if raw_kernel_replay_receipt is not None:
        if raw_replay_input is None or bundle_manifest.replay_input_sha256 is None:
            return False, "kernel_replay_receipt_requires_replay_input", None
        if bundle_manifest.compile_receipt_sha256 is None:
            return False, "kernel_replay_receipt_requires_compile_receipt", None
        if bundle_manifest.kernel_receipt_sha256 is None:
            return False, "kernel_replay_receipt_requires_kernel_receipt", None
        if bundle_manifest.kernel_eval_receipt_sha256 is None:
            return False, "kernel_replay_receipt_requires_kernel_eval_receipt", None
        if bundle_manifest.kernel_settlement_receipt_sha256 is None:
            return False, "kernel_replay_receipt_requires_kernel_settlement_receipt", None
        kernel_replay_ok, kernel_replay_err, _kernel_replay_verification = verify_fire_kernel_replay_receipt(
            raw_kernel_replay_receipt,
            object_manifest=object_manifest,
            object_instance=object_instance,
            replay_input=FireReplayInput.from_dict(raw_replay_input),
            expected_replay_input_sha256=bundle_manifest.replay_input_sha256,
            expected_compile_receipt_sha256=bundle_manifest.compile_receipt_sha256,
            expected_kernel_receipt_sha256=bundle_manifest.kernel_receipt_sha256,
            expected_kernel_eval_receipt_sha256=bundle_manifest.kernel_eval_receipt_sha256,
            expected_kernel_settlement_receipt_sha256=bundle_manifest.kernel_settlement_receipt_sha256,
        )
        if not kernel_replay_ok:
            return False, kernel_replay_err or "kernel_replay_receipt_invalid", None
    replay_input = None
    if raw_proof_tree_cert is not None:
        replay_summary = None
        if raw_replay_input is not None and bundle_manifest.replay_input_sha256 is not None:
            replay_input = FireReplayInput.from_dict(raw_replay_input)
            replay_summary = expected_fire_proof_tree_replay_summary(
                replay_input,
                replay_input_sha256=bundle_manifest.replay_input_sha256,
                kernel_settlement_receipt=raw_kernel_settlement_receipt,
                kernel_settlement_receipt_sha256=bundle_manifest.kernel_settlement_receipt_sha256,
                kernel_replay_receipt=raw_kernel_replay_receipt,
                kernel_replay_receipt_sha256=bundle_manifest.kernel_replay_receipt_sha256,
            )
        proof_ok, proof_err, _proof_verification = verify_fire_proof_tree_certificate(
            raw_proof_tree_cert,
            expected_object_hash=object_manifest.manifest_hash,
            expected_instance_hash=object_instance.instance_hash,
            expected_certificate_sha256=object_manifest.cert_sha256,
            expected_runtime_certificate_summary=summarize_fire_interval_certificate(certificate),
            expected_dependency_hashes=expected_fire_proof_tree_dependency_hashes(object_lock),
            expected_claim_evidence=expected_fire_proof_tree_claim_evidence(object_manifest, certificate),
            expected_integer_eval_summary=expected_fire_proof_tree_integer_eval_summary(
                certificate,
                compile_receipt_sha256=bundle_manifest.compile_receipt_sha256,
                kernel_receipt_sha256=bundle_manifest.kernel_receipt_sha256,
                kernel_eval_receipt_sha256=bundle_manifest.kernel_eval_receipt_sha256,
            ),
            expected_unit_summary=expected_fire_proof_tree_unit_summary(object_manifest),
            expected_replay_summary=replay_summary,
            expected_witness_policy_summary=expected_fire_proof_tree_witness_policy_summary(
                object_manifest,
                contract_receipts=(
                    [item.to_dict() for item in bundle_manifest.contract_receipts]
                    if bundle_manifest.contract_receipts
                    else expected_fire_proof_tree_contract_receipt_summary(object_manifest)
                ),
            ),
            expected_param_summary=expected_fire_proof_tree_param_summary(object_manifest, object_instance),
            expected_authorization_summary=expected_fire_proof_tree_authorization_summary(object_manifest, object_instance),
            expected_nonce_summary=expected_fire_proof_tree_nonce_summary(object_manifest, object_instance),
            expected_maturity_summary=expected_fire_proof_tree_maturity_summary(object_manifest, object_instance),
            expected_window_summary=expected_fire_proof_tree_window_summary(object_manifest, object_instance),
            expected_object_bind_summary=expected_fire_proof_tree_object_bind_summary(
                object_manifest,
                object_manifest_file_sha256=bundle_manifest.object_manifest_file_sha256,
            ),
            expected_instance_bind_summary=expected_fire_proof_tree_instance_bind_summary(
                object_instance,
                object_lock,
                object_instance_file_sha256=bundle_manifest.object_instance_file_sha256,
            ),
            expected_dependency_summary=expected_fire_proof_tree_dependency_summary(
                object_lock,
                object_lock_file_sha256=bundle_manifest.object_lock_file_sha256,
            ),
            certificate_path=root / bundle_manifest.proof_tree_certificate_path
            if bundle_manifest.proof_tree_certificate_path is not None
            else None,
        )
        if not proof_ok:
            return False, proof_err or "proof_tree_certificate_invalid", None
    if raw_replay_input is not None:
        if replay_input is None:
            replay_input = FireReplayInput.from_dict(raw_replay_input)
        replay_ok, replay_err = verify_fire_replay_input(
            replay_input,
            object_manifest=object_manifest,
            object_instance=object_instance,
        )
        if not replay_ok:
            return False, replay_err or "replay_input_invalid", None

    return (
        True,
        None,
        FireObjectPackageVerification(
            bundle_dir=root,
            bundle_manifest=bundle_manifest,
            object_manifest=object_manifest,
            object_instance=object_instance,
            object_lock=object_lock,
            certificate=certificate,
            instance_gate_report=gate_report,
            schema_files=schema_files,
        ),
    )


__all__ = [
    "OBJECT_PACKAGE_CHECK_REPORT_SCHEMA",
    "FireObjectPackageSchemaFiles",
    "FireObjectPackageVerification",
    "fire_object_package_schema_files",
    "verify_fire_object_package",
]
