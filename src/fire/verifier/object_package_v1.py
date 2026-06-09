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


@dataclass(frozen=True)
class _OptionalArtifactSpec:
    """Static description of one optional bundle artifact.

    Carries the per-artifact data for the load/``require_*`` gate AND the schema
    validation. NOTE: the two passes run in DIFFERENT orders in HEAD and both are
    consensus-relevant (each pins which reject code wins on the first fault):

    * Load / ``require_*`` order is this tuple's order (``_OPTIONAL_ARTIFACTS``).
    * Schema-validation order is ``_OPTIONAL_SCHEMA_ORDER`` -- HEAD validated the
      proof-tree certificate's schema BEFORE the receipt schemas, so the proof
      tree comes first there. Do NOT reuse the load order for schema validation.
    """

    field: str  # attribute on _RawArtifacts holding the loaded payload (or None)
    manifest_path_attr: str  # FireRegistryBundleManifest path attribute
    require_flag: str  # keyword in REQUIRE_FLAGS controlling the missing gate
    missing_code: str  # reject code when the section is absent but required
    schema_attr: str  # attribute on FireObjectPackageSchemaFiles for validation
    artifact_name: str  # name used in *_schema_invalid messages


# LOAD / require order. Source order is load-bearing: it reproduces the exact
# first-failure precedence of HEAD's hand-written load sequence (compile, kernel,
# kernel_eval, kernel_settlement, kernel_replay, proof_tree, replay_input).
_OPTIONAL_ARTIFACTS: tuple[_OptionalArtifactSpec, ...] = (
    _OptionalArtifactSpec(
        "compile_receipt", "compile_receipt_path", "require_compile_receipt",
        "compile_receipt_missing", "compile_receipt_schema", "compile_receipt",
    ),
    _OptionalArtifactSpec(
        "kernel_receipt", "kernel_receipt_path", "require_kernel_receipt",
        "kernel_receipt_missing", "kernel_receipt_schema", "kernel_receipt",
    ),
    _OptionalArtifactSpec(
        "kernel_eval_receipt", "kernel_eval_receipt_path", "require_kernel_eval_receipt",
        "kernel_eval_receipt_missing", "kernel_eval_receipt_schema", "kernel_eval_receipt",
    ),
    _OptionalArtifactSpec(
        "kernel_settlement_receipt", "kernel_settlement_receipt_path", "require_kernel_settlement_receipt",
        "kernel_settlement_receipt_missing", "kernel_settlement_receipt_schema", "kernel_settlement_receipt",
    ),
    _OptionalArtifactSpec(
        "kernel_replay_receipt", "kernel_replay_receipt_path", "require_kernel_replay_receipt",
        "kernel_replay_receipt_missing", "kernel_replay_receipt_schema", "kernel_replay_receipt",
    ),
    _OptionalArtifactSpec(
        "proof_tree_cert", "proof_tree_certificate_path", "require_proof_tree_cert",
        "proof_tree_certificate_missing", "proof_tree_certificate_schema", "proof_tree_certificate",
    ),
    _OptionalArtifactSpec(
        "replay_input", "replay_input_path", "require_replay_input",
        "replay_input_missing", "replay_input_schema", "replay_input",
    ),
)

_OPTIONAL_BY_FIELD: dict[str, _OptionalArtifactSpec] = {spec.field: spec for spec in _OPTIONAL_ARTIFACTS}

# SCHEMA-validation order. This deliberately differs from the load order above:
# HEAD validated the proof-tree certificate's schema FIRST among the optionals
# (before the receipt schemas), so a bundle carrying both a bad proof-tree schema
# and a bad receipt schema must reject with ``proof_tree_certificate_schema_invalid``.
# Reusing the load order here silently flips that precedence -- keep these two
# orders separate.
_OPTIONAL_SCHEMA_ORDER: tuple[str, ...] = (
    "proof_tree_cert",
    "compile_receipt",
    "kernel_receipt",
    "kernel_eval_receipt",
    "kernel_settlement_receipt",
    "kernel_replay_receipt",
    "replay_input",
)

# Fail-closed structural invariant: every loadable optional MUST also have a
# schema-validation slot, and vice versa. Without this, adding an optional to
# the load table but forgetting it here would silently skip its schema check
# (a fail-OPEN gap). Enforced at import time with an explicit raise (not assert,
# which `python -O` strips) so a desync can never ship. Module load is the
# shell, not the per-call authority path -- this never runs on untrusted input.
if set(_OPTIONAL_SCHEMA_ORDER) != {spec.field for spec in _OPTIONAL_ARTIFACTS}:
    raise RuntimeError(
        "fire object-package optional artifact tables out of sync: "
        f"load={sorted(spec.field for spec in _OPTIONAL_ARTIFACTS)} "
        f"schema={sorted(_OPTIONAL_SCHEMA_ORDER)}"
    )


@dataclass(frozen=True)
class _RawArtifacts:
    raw_bundle_manifest: Mapping[str, object]
    raw_object_manifest: Mapping[str, object]
    raw_object_instance: Mapping[str, object]
    raw_object_lock: Mapping[str, object]
    raw_certificate: Mapping[str, object]
    optional: Mapping[str, Mapping[str, object] | None]

    def opt(self, field: str) -> Mapping[str, object] | None:
        return self.optional.get(field)


def _load_raw_artifacts(
    root: Path,
    bundle_manifest: FireRegistryBundleManifest,
    require_flags: Mapping[str, bool],
) -> tuple[bool, str | None, _RawArtifacts | None]:
    """Stage 1 of the pipeline: load every raw artifact body.

    Required sections are loaded first (a malformed/missing required body raises,
    matching the original total function). Optional sections are then loaded in
    ``_OPTIONAL_ARTIFACTS`` order; an absent-but-required section returns its
    ``missing_code``. No semantic validation happens here.
    """
    raw_required = {
        "raw_bundle_manifest": _load_json(root / "bundle_manifest.json"),
        "raw_object_manifest": _load_json(root / bundle_manifest.object_manifest_path),
        "raw_object_instance": _load_json(root / bundle_manifest.object_instance_path),
        "raw_object_lock": _load_json(root / bundle_manifest.object_lock_path),
        "raw_certificate": _load_json(root / bundle_manifest.certificate_path),
    }
    optional: dict[str, Mapping[str, object] | None] = {}
    for spec in _OPTIONAL_ARTIFACTS:
        path = getattr(bundle_manifest, spec.manifest_path_attr)
        if path is not None:
            optional[spec.field] = _load_json(root / path)
        else:
            optional[spec.field] = None
            if require_flags[spec.require_flag]:
                return False, spec.missing_code, None
    return True, None, _RawArtifacts(optional=optional, **raw_required)


def _validate_all_schemas(
    raw: _RawArtifacts,
    schema_files: FireObjectPackageSchemaFiles,
) -> tuple[bool, str | None]:
    """Stage 2: schema-validate the required artifacts, then every present
    optional artifact. First failure wins.

    Required artifacts come first, then the optionals in ``_OPTIONAL_SCHEMA_ORDER``
    -- which is HEAD's schema-validation order (proof-tree certificate first),
    NOT the load order. This precedence is consensus-relevant: a bundle with both
    a bad proof-tree schema and a bad receipt schema must reject with the proof
    tree's code.
    """
    validations: list[tuple[str, Mapping[str, object], Path]] = [
        ("object_package", raw.raw_bundle_manifest, schema_files.object_package_schema),
        ("object_manifest", raw.raw_object_manifest, schema_files.object_manifest_schema),
        ("object_instance", raw.raw_object_instance, schema_files.object_instance_schema),
        ("object_lock", raw.raw_object_lock, schema_files.object_lock_schema),
        ("certificate", raw.raw_certificate, schema_files.certificate_schema),
    ]
    for field in _OPTIONAL_SCHEMA_ORDER:
        payload = raw.opt(field)
        if payload is not None:
            spec = _OPTIONAL_BY_FIELD[field]
            validations.append((spec.artifact_name, payload, getattr(schema_files, spec.schema_attr)))
    for artifact_name, payload, schema_path in validations:
        valid, schema_err = _validate_against_schema(payload, schema_path=schema_path, artifact_name=artifact_name)
        if not valid:
            return False, schema_err
    return True, None


def _verify_certificate_gate(
    raw: _RawArtifacts,
    certificate: FireIntervalCertificate,
    object_manifest: FireObjectManifest,
    object_instance: FireObjectInstanceManifest,
) -> tuple[bool, str | None, FireInstanceGateReport | None]:
    """Stage 3: instance gate + certificate instance-gate-claims agreement."""
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
    return True, None, gate_report


def _verify_optional_receipts(
    raw: _RawArtifacts,
    bundle_manifest: FireRegistryBundleManifest,
    object_manifest: FireObjectManifest,
    object_instance: FireObjectInstanceManifest,
) -> tuple[bool, str | None]:
    """Stage 4: compile / kernel / kernel-eval / settlement / replay receipt
    verification (each delegated), preserving the original order and the
    settlement/replay cross-dependency preconditions."""
    raw_compile_receipt = raw.opt("compile_receipt")
    if raw_compile_receipt is not None:
        compile_ok, compile_err, _compile_verification = verify_fire_compile_receipt(
            raw_compile_receipt,
            object_manifest=object_manifest,
            object_instance=object_instance,
        )
        if not compile_ok:
            return False, compile_err or "compile_receipt_invalid"
    raw_kernel_receipt = raw.opt("kernel_receipt")
    if raw_kernel_receipt is not None:
        kernel_ok, kernel_err, _kernel_verification = verify_fire_kernel_receipt(
            raw_kernel_receipt,
            object_manifest=object_manifest,
            object_instance=object_instance,
        )
        if not kernel_ok:
            return False, kernel_err or "kernel_receipt_invalid"
    raw_kernel_eval_receipt = raw.opt("kernel_eval_receipt")
    if raw_kernel_eval_receipt is not None:
        kernel_eval_ok, kernel_eval_err, _kernel_eval_verification = verify_fire_kernel_eval_receipt(
            raw_kernel_eval_receipt,
            object_manifest=object_manifest,
            object_instance=object_instance,
            expected_kernel_receipt_sha256=bundle_manifest.kernel_receipt_sha256,
        )
        if not kernel_eval_ok:
            return False, kernel_eval_err or "kernel_eval_receipt_invalid"
    raw_replay_input = raw.opt("replay_input")
    raw_kernel_settlement_receipt = raw.opt("kernel_settlement_receipt")
    if raw_kernel_settlement_receipt is not None:
        if raw_replay_input is None or bundle_manifest.replay_input_sha256 is None:
            return False, "kernel_settlement_receipt_requires_replay_input"
        if bundle_manifest.kernel_receipt_sha256 is None:
            return False, "kernel_settlement_receipt_requires_kernel_receipt"
        if bundle_manifest.kernel_eval_receipt_sha256 is None:
            return False, "kernel_settlement_receipt_requires_kernel_eval_receipt"
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
            return False, kernel_settlement_err or "kernel_settlement_receipt_invalid"
    raw_kernel_replay_receipt = raw.opt("kernel_replay_receipt")
    if raw_kernel_replay_receipt is not None:
        if raw_replay_input is None or bundle_manifest.replay_input_sha256 is None:
            return False, "kernel_replay_receipt_requires_replay_input"
        if bundle_manifest.compile_receipt_sha256 is None:
            return False, "kernel_replay_receipt_requires_compile_receipt"
        if bundle_manifest.kernel_receipt_sha256 is None:
            return False, "kernel_replay_receipt_requires_kernel_receipt"
        if bundle_manifest.kernel_eval_receipt_sha256 is None:
            return False, "kernel_replay_receipt_requires_kernel_eval_receipt"
        if bundle_manifest.kernel_settlement_receipt_sha256 is None:
            return False, "kernel_replay_receipt_requires_kernel_settlement_receipt"
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
            return False, kernel_replay_err or "kernel_replay_receipt_invalid"
    return True, None


def _verify_proof_tree_stage(
    raw: _RawArtifacts,
    root: Path,
    bundle_manifest: FireRegistryBundleManifest,
    object_manifest: FireObjectManifest,
    object_instance: FireObjectInstanceManifest,
    object_lock: FireObjectDependencyLock,
    certificate: FireIntervalCertificate,
) -> tuple[bool, str | None, FireReplayInput | None]:
    """Stage 5: optional proof-tree certificate verification.

    Returns the ``FireReplayInput`` it constructed (if any) so the replay stage
    can reuse it, exactly as the original threaded ``replay_input`` forward.
    """
    raw_proof_tree_cert = raw.opt("proof_tree_cert")
    if raw_proof_tree_cert is None:
        return True, None, None
    raw_replay_input = raw.opt("replay_input")
    raw_kernel_settlement_receipt = raw.opt("kernel_settlement_receipt")
    raw_kernel_replay_receipt = raw.opt("kernel_replay_receipt")
    replay_input: FireReplayInput | None = None
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
        return False, proof_err or "proof_tree_certificate_invalid", replay_input
    return True, None, replay_input


def _verify_replay_input_stage(
    raw: _RawArtifacts,
    object_manifest: FireObjectManifest,
    object_instance: FireObjectInstanceManifest,
    replay_input: FireReplayInput | None,
) -> tuple[bool, str | None]:
    """Stage 6: optional replay-input verification, reusing any
    ``FireReplayInput`` already built by the proof-tree stage."""
    raw_replay_input = raw.opt("replay_input")
    if raw_replay_input is None:
        return True, None
    if replay_input is None:
        replay_input = FireReplayInput.from_dict(raw_replay_input)
    replay_ok, replay_err = verify_fire_replay_input(
        replay_input,
        object_manifest=object_manifest,
        object_instance=object_instance,
    )
    if not replay_ok:
        return False, replay_err or "replay_input_invalid"
    return True, None


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
    require_flags = {
        "require_compile_receipt": require_compile_receipt,
        "require_kernel_receipt": require_kernel_receipt,
        "require_kernel_eval_receipt": require_kernel_eval_receipt,
        "require_kernel_settlement_receipt": require_kernel_settlement_receipt,
        "require_kernel_replay_receipt": require_kernel_replay_receipt,
        "require_proof_tree_cert": require_proof_tree_cert,
        "require_replay_input": require_replay_input,
    }

    # Stage 1 -- load raw artifact bodies (+ require_* gates).
    load_ok, load_err, raw = _load_raw_artifacts(root, bundle_manifest, require_flags)
    if not load_ok or raw is None:
        return False, load_err, None

    # Stage 2 -- schema-validate required + present-optional artifacts.
    schema_ok, schema_err = _validate_all_schemas(raw, schema_files)
    if not schema_ok:
        return False, schema_err, None

    # Stage 3 -- certificate reconstruction + instance gate / claims agreement.
    certificate = FireIntervalCertificate.from_dict(raw.raw_certificate)
    gate_ok, gate_err, gate_report = _verify_certificate_gate(
        raw, certificate, object_manifest, object_instance
    )
    if not gate_ok or gate_report is None:
        return False, gate_err, None

    # Stage 4 -- delegated receipt verifications (with cross-dependency gates).
    receipts_ok, receipts_err = _verify_optional_receipts(
        raw, bundle_manifest, object_manifest, object_instance
    )
    if not receipts_ok:
        return False, receipts_err, None

    # Stage 5 -- optional proof-tree certificate (threads replay_input forward).
    proof_ok, proof_err, replay_input = _verify_proof_tree_stage(
        raw, root, bundle_manifest, object_manifest, object_instance, object_lock, certificate
    )
    if not proof_ok:
        return False, proof_err, None

    # Stage 6 -- optional replay-input verification.
    replay_ok, replay_err = _verify_replay_input_stage(
        raw, object_manifest, object_instance, replay_input
    )
    if not replay_ok:
        return False, replay_err, None

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
