"""Scoped non-authoritative RISC0 observation for ZenoLedger ProofMetadataV0.

This module closes the caller-boolean boundary for one direct verifier
execution. It deliberately cannot promote ``ProofMetadataV0`` to production
proof authority because that schema does not consensus-bind the DA root,
config digest, authority manifest, registry snapshot, or receipt profile.

Authority flow:

    canonical artifact + metadata + header + caller-selected manifest/registry
      -> one pinned verifier execution
      -> independently recomposed exact facts
      -> private sealed capability
      -> header/checkpoint-bound non-authoritative observation

The observation is suitable for diagnostics and integration plumbing. The
authority manifest digest and registry ID are not committed by the current
ledger profile or replay configuration. No admission API may accept this path
as proof authority.
"""

from __future__ import annotations

import base64
import binascii
import hashlib
import json
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from types import MappingProxyType
from typing import Any, Mapping, NoReturn, final

from src.integration._zeno_ledger_pinned_verifier_process_v1 import (
    DEFAULT_VERIFIER_ADDRESS_SPACE_BYTES,
    DEFAULT_VERIFIER_STACK_BYTES,
    MAX_VERIFIER_STDOUT_BYTES,
    PinnedVerifierProcessError,
    PinnedVerifierProcessFailure,
    VerifierExecutableFormatV1,
    execute_pinned_verifier_once,
)
from src.integration.zeno_ledger_profile import (
    validate_checkpoint_structural_compatibility_v0,
    zeno_ledger_profile_requires_proof_authority_v0,
)
from src.integration.zeno_ledger_v0 import (
    PROOF_METADATA_SCHEMA_V0,
    canonical_header_hash_v0,
    hash_v0,
    proof_metadata_hash_v0,
    validate_checkpoint_header_binding_v0,
    validate_proof_metadata_header_binding_v0,
)
from src.integration.zeno_ledger_verifier_registry_v0 import (
    VERIFIER_STATUS_ACTIVE_V0,
    validate_verifier_registry_v0,
)
from src.state.canonical import canonical_hex_fixed_allow_0x, canonical_json_bytes

AUTHORITY_MANIFEST_SCHEMA_V1 = "zenodex.zeno_ledger.risc0_verifier_authority.v1"
REQUEST_SCHEMA_V1 = "zenodex.zeno_ledger.risc0_direct_verify_request.v1"
RESPONSE_SCHEMA_V1 = "zenodex.zeno_ledger.risc0_direct_verify_response.v1"
OBSERVATION_SCHEMA_V1 = "zenodex.zeno_ledger.proof_verification_observation.v1"

MAX_AUTHORITY_MANIFEST_BYTES = 1024 * 1024
MAX_PROOF_ARTIFACT_BYTES = 16 * 1024 * 1024
MAX_RECEIPT_BYTES = 16 * 1024 * 1024
MAX_JOURNAL_BYTES = 1024 * 1024
MAX_VERIFIER_REQUEST_BYTES = 24 * 1024 * 1024

_PROOF_KIND = "risc0_zkvm_v0"
_PROOF_COMMITMENT_DOMAIN = "risc0_tau_state_proof_envelope_v0"
_TOKEN_CHARS = frozenset("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789._:/-")
_MISSING_PRODUCTION_BINDINGS = (
    "authority_manifest_sha256",
    "canonical_journal_codec",
    "config_digest",
    "data_availability_root",
    "pre_exec_resource_limits",
    "receipt_security_profile",
    "sandboxed_verifier_execution",
    "verifier_registry_id",
)


class AuthenticatedProofVerificationRejectReason(str, Enum):
    """Stable fail-closed rejection classes for direct proof verification."""

    AUTHORITY_MANIFEST_INVALID = "proof_verification.authority_manifest_invalid"
    EXECUTABLE_INVALID = "proof_verification.executable_invalid"
    EXECUTABLE_HASH_MISMATCH = "proof_verification.executable_hash_mismatch"
    PROOF_ARTIFACT_INVALID = "proof_verification.proof_artifact_invalid"
    PROOF_ARTIFACT_MISMATCH = "proof_verification.proof_artifact_mismatch"
    HEADER_BINDING_MISMATCH = "proof_verification.header_binding_mismatch"
    CHECKPOINT_BINDING_MISMATCH = "proof_verification.checkpoint_binding_mismatch"
    AUTHORITY_BINDING_MISMATCH = "proof_verification.authority_binding_mismatch"
    REGISTRY_INVALID = "proof_verification.registry_invalid"
    REGISTRY_SNAPSHOT_MISMATCH = "proof_verification.registry_snapshot_mismatch"
    REGISTRY_ENTRY_REVOKED = "proof_verification.registry_entry_revoked"
    REGISTRY_HEIGHT_INVALID = "proof_verification.registry_height_invalid"
    VERIFIER_PROCESS_FAILED = "proof_verification.verifier_process_failed"
    VERIFIER_TIMEOUT = "proof_verification.verifier_timeout"
    VERIFIER_RESPONSE_INVALID = "proof_verification.verifier_response_invalid"
    VERIFIER_REJECTED = "proof_verification.verifier_rejected"
    VERIFIER_BINDING_MISMATCH = "proof_verification.verifier_binding_mismatch"
    PROFILE_BINDING_MISMATCH = "proof_verification.profile_binding_mismatch"


class ProofVerificationError(ValueError):
    """Typed direct-verification rejection with a stable reason."""

    def __init__(
        self,
        reason: AuthenticatedProofVerificationRejectReason,
        detail: str,
    ) -> None:
        self.reason = reason
        super().__init__(f"{reason.value}: {detail}")


@dataclass(frozen=True, slots=True)
class ProofVerificationObservationV1:
    """Data-only diagnostic projection with no proof or admission authority."""

    schema: str
    status: str
    production_promotable: bool
    missing_production_bindings: tuple[str, ...]
    proof_metadata_schema: str
    chain_id: str
    height: int
    canonical_header_hash: str
    checkpoint_hash: str | None
    header_proof_journal_hash: str
    proof_metadata_hash: str
    proof_artifact_sha256: str
    canonical_receipt_sha256: str
    canonical_journal_sha256: str
    actual_image_id: str
    receipt_kind: str
    hash_function: str
    verifier_parameters_digest: str
    control_id: str
    authority_manifest_sha256: str
    verifier_executable_sha256: str
    verification_request_sha256: str
    registry_id: str
    registry_entry_id: str

    def __post_init__(self) -> None:
        if self.schema != OBSERVATION_SCHEMA_V1:
            raise ValueError("proof verification observation schema mismatch")
        if self.status != "non_authoritative_metadata_v0_risc0_observation":
            raise ValueError("proof verification observation status mismatch")
        if self.production_promotable is not False:
            raise ValueError("ProofMetadataV0 observation cannot be production-promotable")
        if self.missing_production_bindings != _MISSING_PRODUCTION_BINDINGS:
            raise ValueError("ProofMetadataV0 missing-production binding set mismatch")
        if self.proof_metadata_schema != PROOF_METADATA_SCHEMA_V0:
            raise ValueError("proof verification observation metadata schema mismatch")


@dataclass(frozen=True, slots=True)
class _AuthorityPolicyV1:
    executable_sha256: str
    executable_format: VerifierExecutableFormatV1
    registry_id: str
    registry_entry_id: str
    program_id: str
    verifier_id: str
    actual_image_id: str
    receipt_kind: str
    hash_function: str
    verifier_parameters_digest: str
    control_id: str


@dataclass(frozen=True, slots=True)
class _VerifiedFactsV1:
    canonical_facts_json: bytes
    canonical_journal: bytes
    canonical_journal_sha256: str


@dataclass(frozen=True, slots=True)
class _ProofHeaderBindingV1:
    chain_id: str
    height: int
    canonical_header_hash: str
    checkpoint_hash: str | None
    header_proof_journal_hash: str
    proof_metadata_hash: str
    proof_artifact_sha256: str
    canonical_receipt_sha256: str
    actual_image_id: str
    receipt_kind: str
    hash_function: str
    verifier_parameters_digest: str
    control_id: str


@dataclass(frozen=True, slots=True)
class _VerificationProvenanceV1:
    authority_manifest_sha256: str
    verifier_executable_sha256: str
    verification_request_sha256: str
    registry_id: str
    registry_entry_id: str


_AUTHENTICATED_PROOF_VERIFICATION_SEAL = object()


@final
class _AuthenticatedProofVerificationV1:
    """Process-local marker minted only after exact verifier recomposition."""

    __slots__ = ("_facts", "_binding", "_provenance", "_seal")

    def __init__(
        self,
        facts: _VerifiedFactsV1,
        binding: _ProofHeaderBindingV1,
        provenance: _VerificationProvenanceV1,
        *,
        seal: object,
    ) -> None:
        if seal is not _AUTHENTICATED_PROOF_VERIFICATION_SEAL:
            raise TypeError("authenticated proof verification requires the private seal")
        if type(facts) is not _VerifiedFactsV1:
            raise TypeError("facts must be exactly _VerifiedFactsV1")
        if type(binding) is not _ProofHeaderBindingV1:
            raise TypeError("binding must be exactly _ProofHeaderBindingV1")
        if type(provenance) is not _VerificationProvenanceV1:
            raise TypeError("provenance must be exactly _VerificationProvenanceV1")
        object.__setattr__(self, "_facts", facts)
        object.__setattr__(self, "_binding", binding)
        object.__setattr__(self, "_provenance", provenance)
        object.__setattr__(self, "_seal", seal)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("authenticated proof verification cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> None:
        raise AttributeError("authenticated proof verification is immutable")

    def __copy__(self) -> NoReturn:
        raise TypeError("authenticated proof verification cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("authenticated proof verification cannot be copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("authenticated proof verification cannot be serialized")

    def _has_private_seal(self) -> bool:
        try:
            return object.__getattribute__(self, "_seal") is _AUTHENTICATED_PROOF_VERIFICATION_SEAL
        except AttributeError:
            return False


def _mint_authenticated_proof_verification_v1(
    *,
    facts: _VerifiedFactsV1,
    binding: _ProofHeaderBindingV1,
    provenance: _VerificationProvenanceV1,
) -> _AuthenticatedProofVerificationV1:
    return _AuthenticatedProofVerificationV1(
        facts,
        binding,
        provenance,
        seal=_AUTHENTICATED_PROOF_VERIFICATION_SEAL,
    )


def _consume_authenticated_proof_verification_v1(
    authenticated: _AuthenticatedProofVerificationV1,
) -> ProofVerificationObservationV1:
    if type(authenticated) is not _AuthenticatedProofVerificationV1:
        raise TypeError("authenticated must be exactly _AuthenticatedProofVerificationV1")
    if not authenticated._has_private_seal():
        raise TypeError("authenticated proof verification seal mismatch")
    binding = object.__getattribute__(authenticated, "_binding")
    facts = object.__getattribute__(authenticated, "_facts")
    provenance = object.__getattribute__(authenticated, "_provenance")
    return ProofVerificationObservationV1(
        schema=OBSERVATION_SCHEMA_V1,
        status="non_authoritative_metadata_v0_risc0_observation",
        production_promotable=False,
        missing_production_bindings=_MISSING_PRODUCTION_BINDINGS,
        proof_metadata_schema=PROOF_METADATA_SCHEMA_V0,
        chain_id=binding.chain_id,
        height=binding.height,
        canonical_header_hash=binding.canonical_header_hash,
        checkpoint_hash=binding.checkpoint_hash,
        header_proof_journal_hash=binding.header_proof_journal_hash,
        proof_metadata_hash=binding.proof_metadata_hash,
        proof_artifact_sha256=binding.proof_artifact_sha256,
        canonical_receipt_sha256=binding.canonical_receipt_sha256,
        canonical_journal_sha256=facts.canonical_journal_sha256,
        actual_image_id=binding.actual_image_id,
        receipt_kind=binding.receipt_kind,
        hash_function=binding.hash_function,
        verifier_parameters_digest=binding.verifier_parameters_digest,
        control_id=binding.control_id,
        authority_manifest_sha256=provenance.authority_manifest_sha256,
        verifier_executable_sha256=provenance.verifier_executable_sha256,
        verification_request_sha256=provenance.verification_request_sha256,
        registry_id=provenance.registry_id,
        registry_entry_id=provenance.registry_entry_id,
    )


def _validate_required_profile_binding_v1(
    *,
    profile: Mapping[str, Any],
    header: Mapping[str, Any],
    checkpoint: Mapping[str, Any],
    replay_config_digest: str,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    profile_obj = dict(_require_mapping(profile, name="profile"))
    header_obj = dict(_require_mapping(header, name="header"))
    checkpoint_obj = dict(_require_mapping(checkpoint, name="checkpoint"))
    try:
        if not zeno_ledger_profile_requires_proof_authority_v0(profile_obj):
            raise ValueError("profile does not require proof authority")
        validate_checkpoint_header_binding_v0(checkpoint_obj, header_obj)
        validate_checkpoint_structural_compatibility_v0(
            checkpoint=checkpoint_obj,
            profile=profile_obj,
        )
        expected_config_digest = _require_root(
            replay_config_digest,
            name="replay_config_digest",
        )
        if header_obj["config_digest"] != expected_config_digest:
            raise ValueError("header config_digest does not match replay config")
        if header_obj["chain_id"] != profile_obj["chain_id"]:
            raise ValueError("header chain_id does not match profile")
    except (TypeError, ValueError, KeyError) as exc:
        raise ProofVerificationError(
            AuthenticatedProofVerificationRejectReason.PROFILE_BINDING_MISMATCH,
            "authenticated proof is not exactly bound to the required profile",
        ) from exc
    return profile_obj, header_obj, checkpoint_obj


def _consume_profile_bound_proof_observation_v1(
    authenticated: _AuthenticatedProofVerificationV1,
    *,
    profile: Mapping[str, Any],
    header: Mapping[str, Any],
    checkpoint: Mapping[str, Any],
    replay_config_digest: str,
) -> ProofVerificationObservationV1:
    """Project a sealed verifier result into a non-authoritative observation."""

    if type(authenticated) is not _AuthenticatedProofVerificationV1:
        raise TypeError("authenticated must be exactly _AuthenticatedProofVerificationV1")
    if not authenticated._has_private_seal():
        raise TypeError("authenticated proof verification seal mismatch")
    _profile_obj, header_obj, checkpoint_obj = _validate_required_profile_binding_v1(
        profile=profile,
        header=header,
        checkpoint=checkpoint,
        replay_config_digest=replay_config_digest,
    )

    binding = object.__getattribute__(authenticated, "_binding")
    expected_checkpoint_hash = hash_v0("checkpoint_v0", checkpoint_obj)
    expected_header_hash = canonical_header_hash_v0(header_obj)
    if (
        binding.chain_id != header_obj["chain_id"]
        or binding.height != header_obj["height"]
        or binding.canonical_header_hash != expected_header_hash
        or binding.checkpoint_hash != expected_checkpoint_hash
        or binding.header_proof_journal_hash != header_obj["proof_journal_hash"]
    ):
        raise ProofVerificationError(
            AuthenticatedProofVerificationRejectReason.PROFILE_BINDING_MISMATCH,
            "sealed proof binding does not match the required profile header",
        )
    return _consume_authenticated_proof_verification_v1(authenticated)


@final
@dataclass(frozen=True)
class PinnedZenoLedgerRisc0VerifierV1:
    """One diagnostic verifier pinned by exact caller-selected manifest bytes."""

    executable: Path
    authority_manifest_json: bytes
    authority_manifest_sha256: str
    timeout_seconds: int = 60
    max_address_space_bytes: int = DEFAULT_VERIFIER_ADDRESS_SPACE_BYTES
    max_stack_bytes: int = DEFAULT_VERIFIER_STACK_BYTES
    sha256: str = field(init=False)
    executable_format: VerifierExecutableFormatV1 = field(init=False)
    _authority: _AuthorityPolicyV1 = field(init=False, repr=False)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("PinnedZenoLedgerRisc0VerifierV1 cannot be subclassed")

    def __post_init__(self) -> None:
        if not self.executable.is_absolute():
            raise ValueError("ZenoLedger RISC0 verifier executable must be an absolute path")
        _require_bare_sha256(
            self.authority_manifest_sha256,
            name="authority_manifest_sha256",
        )
        if not isinstance(self.timeout_seconds, int) or isinstance(self.timeout_seconds, bool):
            raise TypeError("timeout_seconds must be an int")
        if self.timeout_seconds <= 0 or self.timeout_seconds > 300:
            raise ValueError("timeout_seconds must be in 1..300")
        if self.max_address_space_bytes < 256 * 1024 * 1024:
            raise ValueError("max_address_space_bytes is too small")
        if self.max_stack_bytes < 1024 * 1024:
            raise ValueError("max_stack_bytes is too small")
        authority = _parse_authority_manifest_v1(
            self.authority_manifest_json,
            expected_sha256=self.authority_manifest_sha256,
        )
        object.__setattr__(self, "sha256", authority.executable_sha256)
        object.__setattr__(self, "executable_format", authority.executable_format)
        object.__setattr__(self, "_authority", authority)

    def observe_and_bind_header(
        self,
        *,
        proof_artifact_json: bytes,
        proof_metadata: Mapping[str, Any],
        header: Mapping[str, Any],
        checkpoint: Mapping[str, Any] | None,
        verifier_registry: Mapping[str, Any],
    ) -> ProofVerificationObservationV1:
        """Execute once and return a header-bound non-authoritative observation."""

        authenticated = self._verify_authenticated(
            proof_artifact_json=proof_artifact_json,
            proof_metadata=proof_metadata,
            header=header,
            checkpoint=checkpoint,
            verifier_registry=verifier_registry,
        )
        return _consume_authenticated_proof_verification_v1(authenticated)

    def observe_and_bind_required_profile(
        self,
        *,
        proof_artifact_json: bytes,
        proof_metadata: Mapping[str, Any],
        header: Mapping[str, Any],
        checkpoint: Mapping[str, Any],
        verifier_registry: Mapping[str, Any],
        profile: Mapping[str, Any],
        replay_config_digest: str,
    ) -> ProofVerificationObservationV1:
        """Return an exact profile-bound non-authoritative observation.

        The manifest and registry remain caller-selected because the current
        profile does not commit either identity. Callers must not interpret this
        result as proof authority.
        """

        profile_obj, header_obj, checkpoint_obj = _validate_required_profile_binding_v1(
            profile=profile,
            header=header,
            checkpoint=checkpoint,
            replay_config_digest=replay_config_digest,
        )
        authenticated = self._verify_authenticated(
            proof_artifact_json=proof_artifact_json,
            proof_metadata=proof_metadata,
            header=header_obj,
            checkpoint=checkpoint_obj,
            verifier_registry=verifier_registry,
        )
        return _consume_profile_bound_proof_observation_v1(
            authenticated,
            profile=profile_obj,
            header=header_obj,
            checkpoint=checkpoint_obj,
            replay_config_digest=replay_config_digest,
        )

    def _verify_authenticated(
        self,
        *,
        proof_artifact_json: bytes,
        proof_metadata: Mapping[str, Any],
        header: Mapping[str, Any],
        checkpoint: Mapping[str, Any] | None,
        verifier_registry: Mapping[str, Any],
    ) -> _AuthenticatedProofVerificationV1:
        metadata, header_obj, checkpoint_hash = _validate_header_inputs(
            proof_metadata=proof_metadata,
            header=header,
            checkpoint=checkpoint,
        )
        authority = self._authority
        registry_entry = _select_registry_entry_for_observation(
            registry=verifier_registry,
            authority=authority,
            metadata=metadata,
        )
        artifact, artifact_sha256, receipt_sha256 = _parse_proof_artifact(
            proof_artifact_json,
            expected_commitment=str(metadata["proof_commitment"]),
        )
        expected_facts = _expected_verified_facts(
            artifact_sha256=artifact_sha256,
            receipt_sha256=receipt_sha256,
            metadata=metadata,
            header=header_obj,
            authority=authority,
        )
        request = {
            "schema": REQUEST_SCHEMA_V1,
            "proof_artifact": artifact,
            "expected_verified_facts": expected_facts,
        }
        request_bytes = _bounded_canonical_json_bytes(
            request,
            max_bytes=MAX_VERIFIER_REQUEST_BYTES,
            reason=AuthenticatedProofVerificationRejectReason.PROOF_ARTIFACT_INVALID,
            name="verification request",
        )
        request_sha256 = hashlib.sha256(request_bytes).hexdigest()
        stdout = self._execute_verifier_once(request_bytes)
        verified_facts = _parse_verified_response(
            stdout,
            expected_facts=expected_facts,
        )
        binding = _ProofHeaderBindingV1(
            chain_id=str(header_obj["chain_id"]),
            height=int(header_obj["height"]),
            canonical_header_hash=str(expected_facts["canonical_header_hash"]),
            checkpoint_hash=checkpoint_hash,
            header_proof_journal_hash=str(header_obj["proof_journal_hash"]),
            proof_metadata_hash=str(expected_facts["proof_metadata_hash"]),
            proof_artifact_sha256=artifact_sha256,
            canonical_receipt_sha256=receipt_sha256,
            actual_image_id=authority.actual_image_id,
            receipt_kind=authority.receipt_kind,
            hash_function=authority.hash_function,
            verifier_parameters_digest=authority.verifier_parameters_digest,
            control_id=authority.control_id,
        )
        provenance = _VerificationProvenanceV1(
            authority_manifest_sha256=self.authority_manifest_sha256,
            verifier_executable_sha256=self.sha256,
            verification_request_sha256=request_sha256,
            registry_id=authority.registry_id,
            registry_entry_id=str(registry_entry["entry_id"]),
        )
        authenticated = _mint_authenticated_proof_verification_v1(
            facts=verified_facts,
            binding=binding,
            provenance=provenance,
        )
        return authenticated

    def _execute_verifier_once(self, request_bytes: bytes) -> bytes:
        try:
            return execute_pinned_verifier_once(
                executable=self.executable,
                expected_sha256=self.sha256,
                executable_format=self.executable_format,
                request_bytes=request_bytes,
                timeout_seconds=self.timeout_seconds,
                max_address_space_bytes=self.max_address_space_bytes,
                max_stack_bytes=self.max_stack_bytes,
            )
        except PinnedVerifierProcessError as exc:
            reason_by_failure = {
                PinnedVerifierProcessFailure.EXECUTABLE_INVALID: (
                    AuthenticatedProofVerificationRejectReason.EXECUTABLE_INVALID
                ),
                PinnedVerifierProcessFailure.EXECUTABLE_HASH_MISMATCH: (
                    AuthenticatedProofVerificationRejectReason.EXECUTABLE_HASH_MISMATCH
                ),
                PinnedVerifierProcessFailure.PROCESS_FAILED: (
                    AuthenticatedProofVerificationRejectReason.VERIFIER_PROCESS_FAILED
                ),
                PinnedVerifierProcessFailure.TIMEOUT: (
                    AuthenticatedProofVerificationRejectReason.VERIFIER_TIMEOUT
                ),
                PinnedVerifierProcessFailure.OUTPUT_INVALID: (
                    AuthenticatedProofVerificationRejectReason.VERIFIER_RESPONSE_INVALID
                ),
            }
            raise ProofVerificationError(
                reason_by_failure[exc.reason],
                "pinned verifier process boundary rejected execution",
            ) from exc


def zeno_ledger_risc0_authority_manifest_bytes_v1(
    *,
    executable_sha256: str,
    executable_format: VerifierExecutableFormatV1,
    registry_id: str,
    registry_entry_id: str,
    program_id: str,
    verifier_id: str,
    actual_image_id: str,
    receipt_kind: str,
    hash_function: str,
    verifier_parameters_digest: str,
    control_id: str,
) -> bytes:
    """Build canonical data describing a candidate diagnostic verifier."""

    _require_bare_sha256(executable_sha256, name="executable_sha256")
    if not isinstance(executable_format, VerifierExecutableFormatV1):
        raise ValueError("executable_format is unsupported")
    manifest = {
        "schema": AUTHORITY_MANIFEST_SCHEMA_V1,
        "executable_sha256": executable_sha256,
        "executable_format": executable_format.value,
        "registry_id": _require_root(registry_id, name="registry_id"),
        "registry_entry_id": _require_root(registry_entry_id, name="registry_entry_id"),
        "proof_kind": _PROOF_KIND,
        "program_id": _require_token(program_id, name="program_id"),
        "verifier_id": _require_token(verifier_id, name="verifier_id"),
        "actual_image_id": _require_root(actual_image_id, name="actual_image_id"),
        "receipt_security_profile": {
            "receipt_kind": _require_token(receipt_kind, name="receipt_kind"),
            "hash_function": _require_token(hash_function, name="hash_function"),
            "verifier_parameters_digest": _require_root(
                verifier_parameters_digest,
                name="verifier_parameters_digest",
            ),
            "control_id": _require_root(control_id, name="control_id"),
        },
    }
    raw = canonical_json_bytes(manifest)
    if len(raw) > MAX_AUTHORITY_MANIFEST_BYTES:
        raise ValueError("authority manifest exceeds byte limit")
    _parse_authority_manifest_v1(raw, expected_sha256=hashlib.sha256(raw).hexdigest())
    return raw


def _parse_authority_manifest_v1(
    raw: bytes,
    *,
    expected_sha256: str,
) -> _AuthorityPolicyV1:
    try:
        _require_bare_sha256(expected_sha256, name="expected authority manifest SHA-256")
        manifest = _parse_canonical_json_object(
            raw,
            max_bytes=MAX_AUTHORITY_MANIFEST_BYTES,
            name="authority manifest",
        )
        if hashlib.sha256(raw).hexdigest() != expected_sha256:
            raise ValueError("authority manifest hash mismatch")
        if set(manifest) != {
            "schema",
            "executable_sha256",
            "executable_format",
            "registry_id",
            "registry_entry_id",
            "proof_kind",
            "program_id",
            "verifier_id",
            "actual_image_id",
            "receipt_security_profile",
        }:
            raise ValueError("authority manifest keys mismatch")
        if manifest.get("schema") != AUTHORITY_MANIFEST_SCHEMA_V1:
            raise ValueError("authority manifest schema mismatch")
        if manifest.get("proof_kind") != _PROOF_KIND:
            raise ValueError("authority manifest proof_kind mismatch")
        profile = _require_mapping(
            manifest.get("receipt_security_profile"),
            name="receipt_security_profile",
        )
        if set(profile) != {
            "receipt_kind",
            "hash_function",
            "verifier_parameters_digest",
            "control_id",
        }:
            raise ValueError("receipt_security_profile keys mismatch")
        executable_format = VerifierExecutableFormatV1(manifest.get("executable_format"))
        return _AuthorityPolicyV1(
            executable_sha256=_require_bare_sha256(
                manifest.get("executable_sha256"),
                name="executable_sha256",
            ),
            executable_format=executable_format,
            registry_id=_require_root(manifest.get("registry_id"), name="registry_id"),
            registry_entry_id=_require_root(
                manifest.get("registry_entry_id"),
                name="registry_entry_id",
            ),
            program_id=_require_token(manifest.get("program_id"), name="program_id"),
            verifier_id=_require_token(manifest.get("verifier_id"), name="verifier_id"),
            actual_image_id=_require_root(
                manifest.get("actual_image_id"),
                name="actual_image_id",
            ),
            receipt_kind=_require_token(profile.get("receipt_kind"), name="receipt_kind"),
            hash_function=_require_token(
                profile.get("hash_function"),
                name="hash_function",
            ),
            verifier_parameters_digest=_require_root(
                profile.get("verifier_parameters_digest"),
                name="verifier_parameters_digest",
            ),
            control_id=_require_root(profile.get("control_id"), name="control_id"),
        )
    except (TypeError, ValueError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ProofVerificationError(
            AuthenticatedProofVerificationRejectReason.AUTHORITY_MANIFEST_INVALID,
            "authority manifest is invalid",
        ) from exc


def _validate_header_inputs(
    *,
    proof_metadata: Mapping[str, Any],
    header: Mapping[str, Any],
    checkpoint: Mapping[str, Any] | None,
) -> tuple[dict[str, Any], dict[str, Any], str | None]:
    metadata = dict(_require_mapping(proof_metadata, name="proof_metadata"))
    header_obj = dict(_require_mapping(header, name="header"))
    try:
        validate_proof_metadata_header_binding_v0(metadata, header_obj)
    except (TypeError, ValueError) as exc:
        raise ProofVerificationError(
            AuthenticatedProofVerificationRejectReason.HEADER_BINDING_MISMATCH,
            "ProofMetadataV0 is not exactly bound to the header",
        ) from exc
    if metadata["proof_kind"] != _PROOF_KIND:
        raise ProofVerificationError(
            AuthenticatedProofVerificationRejectReason.AUTHORITY_BINDING_MISMATCH,
            "direct verifier supports only risc0_zkvm_v0",
        )
    checkpoint_hash: str | None = None
    if checkpoint is not None:
        checkpoint_obj = dict(_require_mapping(checkpoint, name="checkpoint"))
        try:
            validate_checkpoint_header_binding_v0(checkpoint_obj, header_obj)
        except (TypeError, ValueError) as exc:
            raise ProofVerificationError(
                AuthenticatedProofVerificationRejectReason.CHECKPOINT_BINDING_MISMATCH,
                "checkpoint is not exactly bound to the header",
            ) from exc
        checkpoint_hash = hash_v0("checkpoint_v0", checkpoint_obj)
    return metadata, header_obj, checkpoint_hash


def _select_registry_entry_for_observation(
    *,
    registry: Mapping[str, Any],
    authority: _AuthorityPolicyV1,
    metadata: Mapping[str, Any],
) -> Mapping[str, Any]:
    registry_obj = dict(_require_mapping(registry, name="verifier_registry"))
    try:
        validate_verifier_registry_v0(registry_obj)
    except (TypeError, ValueError) as exc:
        raise ProofVerificationError(
            AuthenticatedProofVerificationRejectReason.REGISTRY_INVALID,
            "verifier registry is invalid",
        ) from exc
    if registry_obj["registry_id"] != authority.registry_id:
        raise ProofVerificationError(
            AuthenticatedProofVerificationRejectReason.REGISTRY_SNAPSHOT_MISMATCH,
            "verifier registry snapshot is not the governed snapshot",
        )
    selected: Mapping[str, Any] | None = None
    for raw_entry in registry_obj["entries"]:
        entry = _require_mapping(raw_entry, name="verifier_registry entry")
        if entry.get("entry_id") == authority.registry_entry_id:
            selected = entry
            break
    if selected is None:
        raise ProofVerificationError(
            AuthenticatedProofVerificationRejectReason.REGISTRY_SNAPSHOT_MISMATCH,
            "governed registry entry is absent",
        )
    for key, expected in (
        ("proof_kind", _PROOF_KIND),
        ("program_id", authority.program_id),
        ("verifier_id", authority.verifier_id),
    ):
        if selected.get(key) != expected or metadata.get(key) != expected:
            raise ProofVerificationError(
                AuthenticatedProofVerificationRejectReason.AUTHORITY_BINDING_MISMATCH,
                f"metadata, registry, and authority {key} mismatch",
            )
    if selected.get("status") != VERIFIER_STATUS_ACTIVE_V0:
        raise ProofVerificationError(
            AuthenticatedProofVerificationRejectReason.REGISTRY_ENTRY_REVOKED,
            "verifier registry entry is not active",
        )
    height = _require_nonnegative_int(metadata.get("height"), name="metadata.height")
    valid_from = _require_nonnegative_int(
        selected.get("valid_from_height"),
        name="registry.valid_from_height",
    )
    valid_until = selected.get("valid_until_height")
    if height < valid_from or (
        valid_until is not None
        and height > _require_nonnegative_int(valid_until, name="registry.valid_until_height")
    ):
        raise ProofVerificationError(
            AuthenticatedProofVerificationRejectReason.REGISTRY_HEIGHT_INVALID,
            "verifier registry entry is not valid at the header height",
        )
    return MappingProxyType(dict(selected))


def _parse_proof_artifact(
    raw: bytes,
    *,
    expected_commitment: str,
) -> tuple[dict[str, Any], str, str]:
    try:
        artifact = _parse_canonical_json_object(
            raw,
            max_bytes=MAX_PROOF_ARTIFACT_BYTES,
            name="proof artifact",
        )
        proof_b64 = artifact.get("proof")
        if not isinstance(proof_b64, str) or not proof_b64:
            raise ValueError("proof artifact proof must be non-empty base64")
        receipt = base64.b64decode(proof_b64, validate=True)
        if base64.b64encode(receipt).decode("ascii") != proof_b64:
            raise ValueError("proof artifact proof must use canonical base64")
        if not receipt or len(receipt) > MAX_RECEIPT_BYTES:
            raise ValueError("canonical receipt byte length is invalid")
    except (TypeError, ValueError, UnicodeDecodeError, json.JSONDecodeError, binascii.Error) as exc:
        raise ProofVerificationError(
            AuthenticatedProofVerificationRejectReason.PROOF_ARTIFACT_INVALID,
            "proof artifact is not bounded canonical RISC0 envelope JSON",
        ) from exc
    actual_commitment = hash_v0(_PROOF_COMMITMENT_DOMAIN, artifact)
    if actual_commitment != expected_commitment:
        raise ProofVerificationError(
            AuthenticatedProofVerificationRejectReason.PROOF_ARTIFACT_MISMATCH,
            "proof artifact does not match ProofMetadataV0 proof_commitment",
        )
    return (
        artifact,
        hashlib.sha256(raw).hexdigest(),
        hashlib.sha256(receipt).hexdigest(),
    )


def _expected_verified_facts(
    *,
    artifact_sha256: str,
    receipt_sha256: str,
    metadata: Mapping[str, Any],
    header: Mapping[str, Any],
    authority: _AuthorityPolicyV1,
) -> dict[str, object]:
    return {
        "proof_artifact_sha256": artifact_sha256,
        "canonical_receipt_sha256": receipt_sha256,
        "proof_commitment": metadata["proof_commitment"],
        "proof_metadata_hash": proof_metadata_hash_v0(dict(metadata)),
        "header_proof_journal_hash": header["proof_journal_hash"],
        "canonical_header_hash": canonical_header_hash_v0(dict(header)),
        "chain_id": header["chain_id"],
        "height": header["height"],
        "program_id": authority.program_id,
        "verifier_id": authority.verifier_id,
        "actual_image_id": authority.actual_image_id,
        "receipt_kind": authority.receipt_kind,
        "hash_function": authority.hash_function,
        "verifier_parameters_digest": authority.verifier_parameters_digest,
        "control_id": authority.control_id,
        "journal_hash": metadata["journal_hash"],
        "public_input_hash": metadata["public_input_hash"],
        "pre_state_root": metadata["pre_state_root"],
        "post_state_root": metadata["post_state_root"],
        "tx_root": metadata["tx_root"],
        "evidence_root": metadata["evidence_root"],
        "body_root": metadata["body_root"],
        "conflict_schedule_hash": metadata["conflict_schedule_hash"],
        "feature_suite_hash": metadata["feature_suite_hash"],
        "dependency_lock_hash": metadata["dependency_lock_hash"],
        "toolchain_lock_hash": metadata["toolchain_lock_hash"],
    }


def _parse_verified_response(
    raw: bytes,
    *,
    expected_facts: Mapping[str, object],
) -> _VerifiedFactsV1:
    try:
        response = _parse_canonical_json_object(
            raw,
            max_bytes=MAX_VERIFIER_STDOUT_BYTES,
            name="verifier response",
        )
    except (TypeError, ValueError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ProofVerificationError(
            AuthenticatedProofVerificationRejectReason.VERIFIER_RESPONSE_INVALID,
            "verifier response is not bounded canonical JSON",
        ) from exc
    if set(response) != {"schema", "accepted", "journal_b64", "verified_facts"}:
        raise ProofVerificationError(
            AuthenticatedProofVerificationRejectReason.VERIFIER_RESPONSE_INVALID,
            "verifier response keys mismatch",
        )
    if response.get("schema") != RESPONSE_SCHEMA_V1:
        raise ProofVerificationError(
            AuthenticatedProofVerificationRejectReason.VERIFIER_RESPONSE_INVALID,
            "verifier response schema mismatch",
        )
    if response.get("accepted") is not True:
        raise ProofVerificationError(
            AuthenticatedProofVerificationRejectReason.VERIFIER_REJECTED,
            "pinned verifier rejected the proof",
        )
    facts = _require_mapping(response.get("verified_facts"), name="verified_facts")
    if dict(facts) != dict(expected_facts):
        raise ProofVerificationError(
            AuthenticatedProofVerificationRejectReason.VERIFIER_BINDING_MISMATCH,
            "verifier facts do not exactly match host-recomposed expectations",
        )
    journal_b64 = response.get("journal_b64")
    if not isinstance(journal_b64, str) or not journal_b64:
        raise ProofVerificationError(
            AuthenticatedProofVerificationRejectReason.VERIFIER_RESPONSE_INVALID,
            "verifier response journal_b64 is invalid",
        )
    try:
        journal = base64.b64decode(journal_b64, validate=True)
    except (ValueError, binascii.Error) as exc:
        raise ProofVerificationError(
            AuthenticatedProofVerificationRejectReason.VERIFIER_RESPONSE_INVALID,
            "verifier response journal is not canonical base64",
        ) from exc
    if base64.b64encode(journal).decode("ascii") != journal_b64:
        raise ProofVerificationError(
            AuthenticatedProofVerificationRejectReason.VERIFIER_RESPONSE_INVALID,
            "verifier response journal is not canonical base64",
        )
    if not journal or len(journal) > MAX_JOURNAL_BYTES:
        raise ProofVerificationError(
            AuthenticatedProofVerificationRejectReason.VERIFIER_RESPONSE_INVALID,
            "verifier response journal byte length is invalid",
        )
    return _VerifiedFactsV1(
        canonical_facts_json=canonical_json_bytes(dict(facts)),
        canonical_journal=journal,
        canonical_journal_sha256=hashlib.sha256(journal).hexdigest(),
    )


def _parse_canonical_json_object(
    raw: bytes,
    *,
    max_bytes: int,
    name: str,
) -> dict[str, Any]:
    if not isinstance(raw, bytes):
        raise TypeError(f"{name} must be bytes")
    if not raw or len(raw) > max_bytes:
        raise ValueError(f"{name} byte length is invalid")
    decoded = json.loads(
        raw.decode("utf-8"),
        object_pairs_hook=_reject_duplicate_object_keys,
        parse_float=_reject_json_float,
        parse_constant=_reject_json_constant,
    )
    if not isinstance(decoded, dict):
        raise ValueError(f"{name} must decode to an object")
    if canonical_json_bytes(decoded) != raw:
        raise ValueError(f"{name} must use canonical JSON bytes")
    return decoded


def _bounded_canonical_json_bytes(
    value: object,
    *,
    max_bytes: int,
    reason: AuthenticatedProofVerificationRejectReason,
    name: str,
) -> bytes:
    try:
        raw = canonical_json_bytes(value)
    except (TypeError, ValueError, RecursionError) as exc:
        raise ProofVerificationError(reason, f"{name} is not canonical JSON") from exc
    if len(raw) > max_bytes:
        raise ProofVerificationError(reason, f"{name} exceeds byte limit")
    return raw


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a mapping")
    return value


def _require_token(value: object, *, name: str) -> str:
    if not isinstance(value, str) or not value or len(value.encode("utf-8")) > 256:
        raise ValueError(f"{name} must be a non-empty bounded string")
    if any(char not in _TOKEN_CHARS for char in value):
        raise ValueError(f"{name} contains unsupported characters")
    return value


def _require_root(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    return canonical


def _require_bare_sha256(value: object, *, name: str) -> str:
    if (
        not isinstance(value, str)
        or len(value) != 64
        or any(char not in "0123456789abcdef" for char in value)
    ):
        raise ValueError(f"{name} must be lowercase 64-character SHA-256 hex")
    return value


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a non-negative int")
    return value


def _reject_duplicate_object_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_json_float(value: str) -> NoReturn:
    raise ValueError(f"JSON floats are forbidden: {value}")


def _reject_json_constant(value: str) -> NoReturn:
    raise ValueError(f"JSON constants are forbidden: {value}")
