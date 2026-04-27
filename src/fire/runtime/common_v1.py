from __future__ import annotations

from dataclasses import dataclass, fields, is_dataclass
from pathlib import Path
from typing import Any, Callable, TypeVar

from src.fire.registry.bundle_v1 import verify_fire_registry_bundle
from src.fire.registry.instance_v1 import (
    FireObjectInstanceManifest,
    FireObjectParameterValue,
    FireObjectPartyBinding,
)
from src.fire.registry.lock_v1 import build_fire_object_dependency_lock
from src.fire.registry.object_manifest_v1 import (
    FireObjectManifest,
    expected_fire_instance_gate_claims,
    fire_manifest_file_sha256,
    verify_fire_object_manifest,
)
from src.fire.verifier.cert_v1 import (
    FireIntervalCertificate,
    fire_cert_sha256,
    verify_instance_gate_claims,
    verify_interval_certificate,
)
from src.fire.verifier.settlement_v1 import (
    FIRE_SETTLEMENT_AUTHORITY_COMMAND_TAG,
    FireVerifierReceipt,
    fire_witness_binding_hash,
    verify_fire_settlement_authority_receipt,
)


TermsT = TypeVar("TermsT")
ArtifactT = TypeVar("ArtifactT")
StateT = TypeVar("StateT")


@dataclass(frozen=True)
class FireVerifiedArtifactContext:
    manifest: FireObjectManifest
    instance_manifest: FireObjectInstanceManifest
    bundle_hash: str | None = None


def require_bounded_int(name: str, value: object, *, minimum: int = 0, maximum: int) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    out = int(value)
    if out < minimum or out > maximum:
        raise ValueError(f"{name} out of range: {out}")
    return out


def compile_certified_artifact(
    terms: TermsT,
    *,
    build_certificate: Callable[[TermsT], FireIntervalCertificate],
    certificate_env: Callable[[TermsT], Any],
    compile_state: Callable[[TermsT], Any],
    artifact_factory: Callable[..., ArtifactT],
) -> ArtifactT:
    certificate = build_certificate(terms)
    ok, err, interval = verify_interval_certificate(certificate, certificate_env(terms))
    if not ok or interval is None:
        raise RuntimeError(f"certificate build failed: {err or 'unknown error'}")

    state = compile_state(terms)
    if state.artifact_lower != interval.lower or state.artifact_upper != interval.upper:
        raise RuntimeError("compiler/certificate disagreement")

    return artifact_factory(
        terms=terms,
        artifact_lower=interval.lower,
        artifact_upper=interval.upper,
        certificate=certificate,
        cert_sha256=fire_cert_sha256(certificate),
    )


def verify_certified_artifact(
    artifact: Any,
    *,
    expected_ir_hash: str,
    certificate_env: Callable[[Any], Any],
    manifest_builder: Callable[[Any], Any],
    persisted_bundle_dir: str | Path | None = None,
    expected_bundle_hash: str | None = None,
    expected_bundle_file_sha256: str | None = None,
) -> tuple[bool, str | None, FireVerifiedArtifactContext | None]:
    if artifact.ir_hash != expected_ir_hash:
        return False, "ir_hash_mismatch", None
    if artifact.cert_sha256 != fire_cert_sha256(artifact.certificate):
        return False, "cert_sha_mismatch", None

    ok, err, interval = verify_interval_certificate(artifact.certificate, certificate_env(artifact.terms))
    if not ok or interval is None:
        return False, f"certificate_invalid:{err or 'unknown'}", None
    if interval.lower != artifact.artifact_lower or interval.upper != artifact.artifact_upper:
        return False, "artifact_mismatch", None

    manifest = manifest_builder(artifact)
    ok, err = verify_fire_object_manifest(manifest)
    if not ok:
        return False, f"manifest_invalid:{err or 'unknown'}", None
    if getattr(artifact, "manifest_sha256", None) != manifest.manifest_hash:
        return False, "manifest_sha_mismatch", None
    if getattr(artifact, "manifest_file_sha256", None) != fire_manifest_file_sha256(manifest):
        return False, "manifest_file_sha_mismatch", None
    ok, err, _claims = verify_instance_gate_claims(
        artifact.certificate,
        expected=expected_fire_instance_gate_claims(manifest),
        require_present=True,
    )
    if not ok:
        return False, f"certificate_{err or 'instance_gate_claims_invalid'}", None
    if persisted_bundle_dir is not None:
        ok, err, bundle_manifest, bundle_object_manifest, bundle_instance_manifest, _bundle_lock = verify_fire_registry_bundle(
            persisted_bundle_dir,
            expected_bundle_hash=expected_bundle_hash,
            expected_bundle_file_sha256=expected_bundle_file_sha256,
        )
        if not ok or bundle_manifest is None or bundle_object_manifest is None or bundle_instance_manifest is None:
            return False, f"persisted_bundle_invalid:{err or 'unknown'}", None
        if bundle_object_manifest.manifest_hash != manifest.manifest_hash:
            return False, "persisted_bundle_manifest_hash_mismatch", None
        if bundle_object_manifest.cert_sha256 != artifact.cert_sha256:
            return False, "persisted_bundle_cert_hash_mismatch", None
        if bundle_object_manifest.artifact_lower != artifact.artifact_lower:
            return False, "persisted_bundle_artifact_lower_mismatch", None
        if bundle_object_manifest.artifact_upper != artifact.artifact_upper:
            return False, "persisted_bundle_artifact_upper_mismatch", None
        expected_parameters = _artifact_parameter_values(artifact)
        actual_parameters = {item.name: item.value for item in bundle_instance_manifest.parameters}
        if actual_parameters != expected_parameters:
            return False, "persisted_bundle_instance_parameters_mismatch", None
        return True, None, FireVerifiedArtifactContext(
            manifest=manifest,
            instance_manifest=bundle_instance_manifest,
            bundle_hash=bundle_manifest.bundle_hash,
        )
    return True, None, FireVerifiedArtifactContext(
        manifest=manifest,
        instance_manifest=_build_default_instance_manifest(manifest, artifact),
        bundle_hash=None,
    )


def _artifact_parameter_values(artifact: Any) -> dict[str, int]:
    terms = getattr(artifact, "terms", None)
    if terms is None:
        raise TypeError("artifact missing terms")
    if is_dataclass(terms):
        return {field.name: int(getattr(terms, field.name)) for field in fields(terms)}
    if hasattr(terms, "__dict__"):
        return {
            str(name): int(value)
            for name, value in vars(terms).items()
            if isinstance(value, int) and not isinstance(value, bool)
        }
    raise TypeError("artifact terms must be a dataclass or object with __dict__")


def _build_default_instance_manifest(manifest: FireObjectManifest, artifact: Any) -> FireObjectInstanceManifest:
    lock = build_fire_object_dependency_lock(manifest)
    parameters = tuple(
        FireObjectParameterValue(name=name, value=value)
        for name, value in sorted(_artifact_parameter_values(artifact).items())
    )
    parties = (
        FireObjectPartyBinding(role="holder", party_id="role:holder"),
        FireObjectPartyBinding(role="writer", party_id="role:writer"),
    )
    return FireObjectInstanceManifest.build(
        object_hash=manifest.manifest_hash,
        lock_hash=lock.lock_hash,
        object_name=manifest.object_name,
        object_version=manifest.object_version,
        object_family=manifest.object_family,
        parameters=parameters,
        parties=parties,
        nonce=f"bundle:{manifest.object_name}:{manifest.object_version}",
        maturity=None,
        settlement_window=None,
    )


def run_verified_settlement(
    artifact: Any,
    *,
    expected_ir_hash: str,
    certificate_env: Callable[[Any], Any],
    manifest_builder: Callable[[Any], Any],
    persisted_bundle_dir: str | Path | None = None,
    expected_bundle_hash: str | None = None,
    expected_bundle_file_sha256: str | None = None,
    compiled_state_from_artifact: Callable[[Any], StateT],
    ref_module: Any,
    settle_args: dict[str, int],
    witness_inputs: Mapping[str, object] | None = None,
    command_tag: str = FIRE_SETTLEMENT_AUTHORITY_COMMAND_TAG,
) -> tuple[bool, str | None, StateT | None, FireVerifierReceipt | None]:
    ok, err, context = verify_certified_artifact(
        artifact,
        expected_ir_hash=expected_ir_hash,
        certificate_env=certificate_env,
        manifest_builder=manifest_builder,
        persisted_bundle_dir=persisted_bundle_dir,
        expected_bundle_hash=expected_bundle_hash,
        expected_bundle_file_sha256=expected_bundle_file_sha256,
    )
    if not ok or context is None:
        return False, err, None, None

    try:
        compiled_state = compiled_state_from_artifact(artifact)
    except RuntimeError as exc:
        return False, str(exc), None, None

    result = ref_module.step(
        compiled_state,
        ref_module.Command(
            tag=command_tag,
            args=dict(settle_args),
        ),
    )
    if not result.ok or result.state is None:
        return False, result.error or "settlement_rejected", None, None
    if command_tag == FIRE_SETTLEMENT_AUTHORITY_COMMAND_TAG and witness_inputs is None:
        return False, "witness_inputs_missing", None, None
    try:
        witness_hash = None if witness_inputs is None else fire_witness_binding_hash(witness_inputs)
    except (TypeError, ValueError) as exc:
        return False, f"witness_binding_invalid:{exc}", None, None
    receipt = FireVerifierReceipt.build(
        object_hash=context.manifest.manifest_hash,
        instance_hash=context.instance_manifest.instance_hash,
        cert_sha256=artifact.cert_sha256,
        holder_delta=int(getattr(result.state, "holder_delta")),
        writer_delta=int(getattr(result.state, "writer_delta")),
        command_tag=command_tag,
        object_name=context.manifest.object_name,
        object_version=context.manifest.object_version,
        bundle_hash=context.bundle_hash,
        witness_hash=witness_hash,
    )
    ok, err = verify_fire_settlement_authority_receipt(
        receipt,
        expected_object_hash=context.manifest.manifest_hash,
        expected_instance_hash=context.instance_manifest.instance_hash,
        expected_cert_sha256=artifact.cert_sha256,
        expected_holder_delta=int(getattr(result.state, "holder_delta")),
        expected_writer_delta=int(getattr(result.state, "writer_delta")),
        expected_command_tag=command_tag,
        expected_bundle_hash=context.bundle_hash,
        expected_witness_hash=witness_hash,
    )
    if not ok:
        return False, f"verifier_receipt_{err or 'invalid'}", None, None
    return True, None, result.state, receipt


__all__ = [
    "FireVerifiedArtifactContext",
    "compile_certified_artifact",
    "require_bounded_int",
    "run_verified_settlement",
    "verify_certified_artifact",
]
