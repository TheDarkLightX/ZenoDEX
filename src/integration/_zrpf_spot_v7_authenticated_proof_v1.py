"""Authority-neutral observation from one caller-pinned Spot V7 verifier.

The Rust verifier is expected to authenticate the canonical V7 receipt and its
exact V6 child once. This adapter pins the selected executable, checks every
emitted artifact association, and retains a process-local observation. The
caller-selected executable and manifest are not a governed trust root.

Proof authority requires a later atomic consumer to bind this exact executable
and manifest to the transaction-locked current release. Data availability,
external finality, Firecracker execution, release currentness, economic commit,
settlement authority, and production authority are also separate obligations.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Mapping, NoReturn, SupportsIndex, final

from src.integration._zeno_ledger_pinned_verifier_process_v1 import (
    PinnedVerifierProcessError,
    VerifierExecutableFormatV1,
    execute_pinned_verifier_once,
)
from src.integration.recursive_stark_verifier_adapter import (
    DEFAULT_VERIFIER_ADDRESS_SPACE_BYTES,
    DEFAULT_VERIFIER_STACK_BYTES,
    MAX_AUTHORITY_MANIFEST_BYTES,
    RecursiveVerifierExecutableFormat,
    _reject_duplicate_object_keys,
    _reject_json_constant,
)
from src.state.canonical import canonical_json_bytes
from tools.zrpf_spot_v7_verifier_payload_codec import (
    SPOT_V7_VERIFIER_PAYLOAD_CAP_BYTES_V1,
    SpotV7FirecrackerProtocolRejectV1,
    decode_structural_v7_verifier_payload_v1,
)

SPOT_V7_PROOF_VERIFIER_REQUEST_SCHEMA_V1 = "zenodex.zrpf_spot_v7_proof_verifier.request.v1"
SPOT_V7_PROOF_VERIFIER_RESPONSE_SCHEMA_V1 = "zenodex.zrpf_spot_v7_proof_verifier.response.v1"
SPOT_V7_PROOF_VERIFIER_AUTHORITY_MANIFEST_SCHEMA_V1 = (
    "zenodex.zrpf_spot_v7_proof_verifier_authority.v1"
)

MAX_SPOT_V7_RECEIPT_BYTES_V1 = 16 * 1_024 * 1_024
MAX_SPOT_V7_SOURCE_V6_RECEIPT_BYTES_V1 = 16 * 1_024 * 1_024
MAX_SPOT_V7_GUEST_INPUT_BYTES_V1 = (
    18
    + (971 + 1_024 + 8 * 1_024 * 1_024)
    + 512
    + 8 * 1_024 * 1_024
    + (2 + 28 + 16_384 * (96 + 156 + 96) + 64)
)
MAX_SPOT_V7_PROOF_REQUEST_BYTES_V1 = 128 * 1_024 * 1_024
MAX_SPOT_V7_PROOF_RESPONSE_BYTES_V1 = 256 * 1_024
MAX_SPOT_V7_CONSUMED_OBJECTS_V1 = 128

_ACTION_IDS_ROOT_DOMAIN_V1 = b"zenodex.zrpf.economic_action_ids_root.v1"
_ACTION_BINDINGS_ROOT_DOMAIN_V1 = b"zenodex.zrpf.action_authorization_bindings_root.v1"
_GRANT_SPENDS_ROOT_DOMAIN_V1 = b"zenodex.zrpf.authorization_grant_spends_root.v1"
_CONSUMED_OBJECTS_ROOT_DOMAIN_V1 = b"zenodex.zrpf.economic_consumed_objects_root.v1"

_AUTHORITY_KEYS = frozenset(
    {
        "schema",
        "executable_sha256",
        "executable_format",
        "application_id",
        "chain_or_domain_id",
        "epoch_id",
        "verified_program_id",
        "verified_profile_id",
        "verified_program_manifest_root",
        "receipt_security_profile",
        "source_child_program_id",
        "required_source_child_receipt_security_profile_id",
    }
)
_RECEIPT_PROFILE_KEYS = frozenset(
    {"profile_id", "receipt_kind", "verifier_parameters", "hashfn", "control_id"}
)
_RECEIPT_PROFILE_KEYS_IN_RUST_ORDER = (
    "profile_id",
    "receipt_kind",
    "verifier_parameters",
    "hashfn",
    "control_id",
)
_PROJECTION_KEYS_IN_RUST_ORDER = (
    "request_bytes",
    "request_sha256",
    "v7_receipt_bytes",
    "v7_receipt_sha256",
    "guest_input_bytes",
    "guest_input_sha256",
    "source_v6_receipt_bytes",
    "source_v6_receipt_sha256",
    "verifier_output_bytes",
    "verifier_output_hex",
    "verifier_output_sha256",
    "journal_bytes",
    "journal_sha256",
    "plan_b_bytes",
    "plan_b_sha256",
    "verified_program_id",
    "verified_profile_id",
    "verified_program_manifest_root",
    "receipt_security_profile",
    "source_child_program_id",
    "required_source_child_receipt_security_profile_id",
    "source_child_claim_binding",
    "source_child_journal_sha256",
    "application_id",
    "chain_or_domain_id",
    "epoch_id",
    "data_availability_certificate_root",
    "data_root",
    "settlement_effect_plan_commitment",
    "economic_action_id",
    "authorization_nullifier",
    "authorization_grant_spend_nullifier",
    "consumed_object_ids",
    "action_ids_root",
    "action_authorization_bindings_root",
    "authorization_grant_spends_root",
    "consumed_object_ids_root",
    "cell_transitions_root",
    "pre_state_root",
    "post_state_root",
)


class SpotV7SemanticProofVerificationErrorV1(ValueError):
    """Stable fail-closed rejection at the pinned Spot V7 proof boundary."""


@dataclass(frozen=True, slots=True)
class _ReceiptSecurityProfileV1:
    profile_id: str
    receipt_kind: str
    verifier_parameters: str
    hashfn: str
    control_id: str


@dataclass(frozen=True, slots=True)
class _TrustedSpotV7ProofPolicyV1:
    application_id: str
    chain_or_domain_id: str
    epoch_id: int
    verified_program_id: str
    verified_profile_id: str
    verified_program_manifest_root: str
    receipt_security_profile: _ReceiptSecurityProfileV1
    source_child_program_id: str
    required_source_child_receipt_security_profile_id: str


@dataclass(frozen=True, slots=True)
class _PinnedSpotV7ProofProjectionDataV1:
    application_id: str
    chain_or_domain_id: str
    epoch_id: int
    verified_program_id: str
    verified_profile_id: str
    verified_program_manifest_root: str
    receipt_security_profile: _ReceiptSecurityProfileV1
    source_child_program_id: str
    required_source_child_receipt_security_profile_id: str
    source_child_claim_binding: str
    source_child_journal_sha256: str
    data_availability_certificate_root: str
    data_root: str
    settlement_effect_plan_commitment: str
    economic_action_id: str
    authorization_nullifier: str
    authorization_grant_spend_nullifier: str
    consumed_object_ids: tuple[str, ...]
    action_ids_root: str
    action_authorization_bindings_root: str
    authorization_grant_spends_root: str
    consumed_object_ids_root: str
    cell_transitions_root: str
    pre_state_root: str
    post_state_root: str
    exact_v7_receipt_bytes: bytes
    exact_guest_input_bytes: bytes
    exact_source_v6_receipt_bytes: bytes
    exact_verifier_output_bytes: bytes
    exact_v7_journal_bytes: bytes
    exact_plan_b_bytes: bytes
    proof_verifier_authority_manifest_sha256: str
    proof_verifier_executable_sha256: str
    proof_verification_request_sha256: str
    proof_verification_response_sha256: str


class _PinnedSpotV7SemanticProofObservationSealV1:
    __slots__ = ()


_PINNED_SPOT_V7_SEMANTIC_PROOF_OBSERVATION_SEAL_V1 = _PinnedSpotV7SemanticProofObservationSealV1()


@final
class _PinnedSpotV7SemanticProofObservationV1:
    """Opaque process-local observation carrying no proof authority."""

    __slots__ = ("_projection", "_seal")

    _projection: _PinnedSpotV7ProofProjectionDataV1
    _seal: _PinnedSpotV7SemanticProofObservationSealV1

    def __init__(
        self,
        projection: _PinnedSpotV7ProofProjectionDataV1,
        *,
        seal: _PinnedSpotV7SemanticProofObservationSealV1,
    ) -> None:
        if seal is not _PINNED_SPOT_V7_SEMANTIC_PROOF_OBSERVATION_SEAL_V1:
            raise TypeError("pinned Spot V7 proof observation requires its private seal")
        if type(projection) is not _PinnedSpotV7ProofProjectionDataV1:
            raise TypeError("pinned Spot V7 proof projection has the wrong type")
        object.__setattr__(self, "_projection", projection)
        object.__setattr__(self, "_seal", seal)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("_PinnedSpotV7SemanticProofObservationV1 cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("pinned Spot V7 proof observation cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("pinned Spot V7 proof observation cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("pinned Spot V7 proof observation cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("pinned Spot V7 proof observation cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("pinned Spot V7 proof observation cannot be serialized")

    def _has_private_seal(self) -> bool:
        return (
            object.__getattribute__(self, "_seal")
            is _PINNED_SPOT_V7_SEMANTIC_PROOF_OBSERVATION_SEAL_V1
        )

    @property
    def pinned_verifier_execution_observed(self) -> bool:
        return self._has_private_seal()

    @property
    def release_governed_verifier_identity_verified(self) -> bool:
        return False

    @property
    def proof_receipt_authority(self) -> bool:
        return False

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False

    @property
    def application_id(self) -> str:
        return self._projection.application_id

    @property
    def chain_or_domain_id(self) -> str:
        return self._projection.chain_or_domain_id

    @property
    def epoch_id(self) -> int:
        return self._projection.epoch_id

    @property
    def verified_program_id(self) -> str:
        return self._projection.verified_program_id

    @property
    def verified_profile_id(self) -> str:
        return self._projection.verified_profile_id

    @property
    def verified_program_manifest_root(self) -> str:
        return self._projection.verified_program_manifest_root

    @property
    def receipt_security_profile(self) -> _ReceiptSecurityProfileV1:
        return self._projection.receipt_security_profile

    @property
    def source_child_program_id(self) -> str:
        return self._projection.source_child_program_id

    @property
    def required_source_child_receipt_security_profile_id(self) -> str:
        return self._projection.required_source_child_receipt_security_profile_id

    @property
    def source_child_claim_binding(self) -> str:
        return self._projection.source_child_claim_binding

    @property
    def source_child_journal_sha256(self) -> str:
        return self._projection.source_child_journal_sha256

    @property
    def data_availability_certificate_root(self) -> str:
        return self._projection.data_availability_certificate_root

    @property
    def data_root(self) -> str:
        return self._projection.data_root

    @property
    def settlement_effect_plan_commitment(self) -> str:
        return self._projection.settlement_effect_plan_commitment

    @property
    def economic_action_id(self) -> str:
        return self._projection.economic_action_id

    @property
    def authorization_nullifier(self) -> str:
        return self._projection.authorization_nullifier

    @property
    def authorization_grant_spend_nullifier(self) -> str:
        return self._projection.authorization_grant_spend_nullifier

    @property
    def consumed_object_ids(self) -> tuple[str, ...]:
        return self._projection.consumed_object_ids

    @property
    def action_ids_root(self) -> str:
        return self._projection.action_ids_root

    @property
    def action_authorization_bindings_root(self) -> str:
        return self._projection.action_authorization_bindings_root

    @property
    def authorization_grant_spends_root(self) -> str:
        return self._projection.authorization_grant_spends_root

    @property
    def consumed_object_ids_root(self) -> str:
        return self._projection.consumed_object_ids_root

    @property
    def cell_transitions_root(self) -> str:
        return self._projection.cell_transitions_root

    @property
    def pre_state_root(self) -> str:
        return self._projection.pre_state_root

    @property
    def post_state_root(self) -> str:
        return self._projection.post_state_root

    @property
    def receipt_sha256(self) -> str:
        return hashlib.sha256(self._projection.exact_v7_receipt_bytes).hexdigest()

    @property
    def journal_sha256(self) -> str:
        return hashlib.sha256(self._projection.exact_v7_journal_bytes).hexdigest()

    @property
    def exact_v7_receipt_bytes(self) -> bytes:
        return self._projection.exact_v7_receipt_bytes

    @property
    def exact_guest_input_bytes(self) -> bytes:
        return self._projection.exact_guest_input_bytes

    @property
    def exact_source_v6_receipt_bytes(self) -> bytes:
        return self._projection.exact_source_v6_receipt_bytes

    @property
    def exact_verifier_output_bytes(self) -> bytes:
        return self._projection.exact_verifier_output_bytes

    @property
    def exact_v7_journal_bytes(self) -> bytes:
        return self._projection.exact_v7_journal_bytes

    @property
    def exact_plan_b_bytes(self) -> bytes:
        return self._projection.exact_plan_b_bytes

    @property
    def proof_verifier_authority_manifest_sha256(self) -> str:
        return self._projection.proof_verifier_authority_manifest_sha256

    @property
    def proof_verifier_executable_sha256(self) -> str:
        return self._projection.proof_verifier_executable_sha256

    @property
    def proof_verification_request_sha256(self) -> str:
        return self._projection.proof_verification_request_sha256

    @property
    def proof_verification_response_sha256(self) -> str:
        return self._projection.proof_verification_response_sha256


@final
@dataclass(frozen=True)
class PinnedSpotV7SemanticProofVerifierV1:
    """Pinned executable and governed expectations for one V7 proof."""

    executable: Path
    authority_manifest_json: bytes
    authority_manifest_sha256: str
    timeout_seconds: int = 60
    max_address_space_bytes: int = DEFAULT_VERIFIER_ADDRESS_SPACE_BYTES
    max_stack_bytes: int = DEFAULT_VERIFIER_STACK_BYTES
    sha256: str = field(init=False)
    executable_format: RecursiveVerifierExecutableFormat = field(init=False)
    trusted_policy: _TrustedSpotV7ProofPolicyV1 = field(init=False)
    _canonical_policy_json: bytes = field(init=False, repr=False)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("PinnedSpotV7SemanticProofVerifierV1 cannot be subclassed")

    def __post_init__(self) -> None:
        if not isinstance(self.executable, Path) or not self.executable.is_absolute():
            raise ValueError("Spot V7 proof verifier executable must be an absolute Path")
        _require_bare_hash(self.authority_manifest_sha256, "authority manifest SHA-256")
        if type(self.timeout_seconds) is not int or not 1 <= self.timeout_seconds <= 300:
            raise ValueError("Spot V7 proof verifier timeout must be in 1..300")
        if (
            type(self.max_address_space_bytes) is not int
            or self.max_address_space_bytes < 256 * 1_024 * 1_024
        ):
            raise ValueError("Spot V7 proof verifier address-space limit is too small")
        if type(self.max_stack_bytes) is not int or self.max_stack_bytes < 1_024 * 1_024:
            raise ValueError("Spot V7 proof verifier stack limit is too small")
        executable_sha256, executable_format, policy, policy_json = _parse_authority_manifest(
            self.authority_manifest_json,
            expected_sha256=self.authority_manifest_sha256,
        )
        object.__setattr__(self, "sha256", executable_sha256)
        object.__setattr__(self, "executable_format", executable_format)
        object.__setattr__(self, "trusted_policy", policy)
        object.__setattr__(self, "_canonical_policy_json", policy_json)

    def verify(
        self,
        *,
        v7_receipt: bytes,
        guest_input: bytes,
        source_v6_receipt: bytes,
    ) -> _PinnedSpotV7SemanticProofObservationV1:
        """Run one pinned verifier exactly once and return an authority-neutral observation."""

        if self.executable_format is not RecursiveVerifierExecutableFormat.STATIC_ELF_X86_64:
            raise SpotV7SemanticProofVerificationErrorV1(
                "durable Spot V7 proof verification requires a static ELF verifier"
            )
        request = spot_v7_proof_verifier_request_bytes_v1(
            v7_receipt=v7_receipt,
            guest_input=guest_input,
            source_v6_receipt=source_v6_receipt,
        )
        try:
            response = execute_pinned_verifier_once(
                executable=self.executable,
                expected_sha256=self.sha256,
                executable_format=VerifierExecutableFormatV1(self.executable_format.value),
                request_bytes=request,
                timeout_seconds=self.timeout_seconds,
                max_address_space_bytes=self.max_address_space_bytes,
                max_stack_bytes=self.max_stack_bytes,
                max_stdout_bytes=MAX_SPOT_V7_PROOF_RESPONSE_BYTES_V1,
            )
        except PinnedVerifierProcessError as exc:
            raise SpotV7SemanticProofVerificationErrorV1(
                f"pinned Spot V7 proof verifier failed: {exc.reason.value}"
            ) from exc
        projection = _parse_authenticated_response(
            response,
            request=request,
            v7_receipt=v7_receipt,
            guest_input=guest_input,
            source_v6_receipt=source_v6_receipt,
            policy=self.trusted_policy,
            authority_manifest_sha256=self.authority_manifest_sha256,
            executable_sha256=self.sha256,
        )
        return _PinnedSpotV7SemanticProofObservationV1(
            projection,
            seal=_PINNED_SPOT_V7_SEMANTIC_PROOF_OBSERVATION_SEAL_V1,
        )


def spot_v7_proof_verifier_request_bytes_v1(
    *,
    v7_receipt: bytes,
    guest_input: bytes,
    source_v6_receipt: bytes,
) -> bytes:
    """Build the exact Rust request-field order and byte framing."""

    _require_exact_bytes(
        v7_receipt,
        maximum=MAX_SPOT_V7_RECEIPT_BYTES_V1,
        name="V7 receipt",
    )
    _require_exact_bytes(
        guest_input,
        maximum=MAX_SPOT_V7_GUEST_INPUT_BYTES_V1,
        name="V7 guest input",
    )
    _require_exact_bytes(
        source_v6_receipt,
        maximum=MAX_SPOT_V7_SOURCE_V6_RECEIPT_BYTES_V1,
        name="source V6 receipt",
    )
    raw = _rust_json_bytes(
        {
            "schema": SPOT_V7_PROOF_VERIFIER_REQUEST_SCHEMA_V1,
            "v7_receipt_hex": v7_receipt.hex(),
            "guest_input_hex": guest_input.hex(),
            "source_v6_receipt_hex": source_v6_receipt.hex(),
        }
    )
    if len(raw) > MAX_SPOT_V7_PROOF_REQUEST_BYTES_V1:
        raise SpotV7SemanticProofVerificationErrorV1(
            "Spot V7 proof verifier request exceeds its byte bound"
        )
    return raw


def spot_v7_proof_verifier_authority_manifest_bytes_v1(
    *,
    executable_sha256: str,
    application_id: str,
    chain_or_domain_id: str,
    epoch_id: int,
    verified_program_id: str,
    verified_profile_id: str,
    verified_program_manifest_root: str,
    receipt_security_profile: Mapping[str, object],
    source_child_program_id: str,
    required_source_child_receipt_security_profile_id: str,
    executable_format: RecursiveVerifierExecutableFormat = (
        RecursiveVerifierExecutableFormat.STATIC_ELF_X86_64
    ),
) -> bytes:
    """Build one canonical, replaceable verifier-authority manifest."""

    if type(executable_format) is not RecursiveVerifierExecutableFormat:
        raise ValueError("Spot V7 proof verifier executable format is invalid")
    policy = _validate_policy_fields(
        {
            "application_id": application_id,
            "chain_or_domain_id": chain_or_domain_id,
            "epoch_id": epoch_id,
            "verified_program_id": verified_program_id,
            "verified_profile_id": verified_profile_id,
            "verified_program_manifest_root": verified_program_manifest_root,
            "receipt_security_profile": receipt_security_profile,
            "source_child_program_id": source_child_program_id,
            "required_source_child_receipt_security_profile_id": (
                required_source_child_receipt_security_profile_id
            ),
        }
    )
    _require_bare_hash(executable_sha256, "executable_sha256")
    value = {
        "schema": SPOT_V7_PROOF_VERIFIER_AUTHORITY_MANIFEST_SCHEMA_V1,
        "executable_sha256": executable_sha256,
        "executable_format": executable_format.value,
        **_policy_to_json(policy),
    }
    raw = canonical_json_bytes(value)
    if len(raw) > MAX_AUTHORITY_MANIFEST_BYTES:
        raise ValueError("Spot V7 proof verifier authority manifest is too large")
    return raw


def _parse_authority_manifest(
    raw: bytes,
    *,
    expected_sha256: str,
) -> tuple[
    str,
    RecursiveVerifierExecutableFormat,
    _TrustedSpotV7ProofPolicyV1,
    bytes,
]:
    if type(raw) is not bytes or not raw or len(raw) > MAX_AUTHORITY_MANIFEST_BYTES:
        raise ValueError("Spot V7 proof verifier authority manifest length is invalid")
    if hashlib.sha256(raw).hexdigest() != expected_sha256:
        raise ValueError("Spot V7 proof verifier authority manifest hash mismatch")
    value = _decode_strict_json_object(raw, "authority manifest")
    if canonical_json_bytes(value) != raw:
        raise ValueError("Spot V7 proof verifier authority manifest must be canonical JSON")
    if set(value) != _AUTHORITY_KEYS:
        raise ValueError("Spot V7 proof verifier authority manifest schema mismatch")
    if value.get("schema") != SPOT_V7_PROOF_VERIFIER_AUTHORITY_MANIFEST_SCHEMA_V1:
        raise ValueError("Spot V7 proof verifier authority manifest schema unsupported")
    executable_sha256 = _mapping_string(value, "executable_sha256")
    _require_bare_hash(executable_sha256, "manifest executable_sha256")
    try:
        executable_format = RecursiveVerifierExecutableFormat(
            _mapping_string(value, "executable_format")
        )
    except ValueError as exc:
        raise ValueError("Spot V7 proof verifier executable format unsupported") from exc
    policy = _validate_policy_fields(
        {
            key: value[key]
            for key in value
            if key not in {"schema", "executable_sha256", "executable_format"}
        }
    )
    policy_json = canonical_json_bytes(_policy_to_json(policy))
    return executable_sha256, executable_format, policy, policy_json


def _parse_authenticated_response(
    raw: bytes,
    *,
    request: bytes,
    v7_receipt: bytes,
    guest_input: bytes,
    source_v6_receipt: bytes,
    policy: _TrustedSpotV7ProofPolicyV1,
    authority_manifest_sha256: str,
    executable_sha256: str,
) -> _PinnedSpotV7ProofProjectionDataV1:
    if type(raw) is not bytes or not raw or len(raw) > MAX_SPOT_V7_PROOF_RESPONSE_BYTES_V1:
        raise SpotV7SemanticProofVerificationErrorV1(
            "Spot V7 proof verifier response length is invalid"
        )
    response = _decode_strict_json_object(raw, "proof verifier response")
    if _rust_json_bytes(response) != raw:
        raise SpotV7SemanticProofVerificationErrorV1(
            "Spot V7 proof verifier response must be canonical JSON"
        )
    if list(response) != ["ok", "schema", "authenticated_projection"]:
        raise SpotV7SemanticProofVerificationErrorV1(
            "Spot V7 proof verifier response field order mismatch"
        )
    if response.get("ok") is not True or (
        response.get("schema") != SPOT_V7_PROOF_VERIFIER_RESPONSE_SCHEMA_V1
    ):
        raise SpotV7SemanticProofVerificationErrorV1(
            "Spot V7 proof verifier response schema mismatch"
        )
    values = response.get("authenticated_projection")
    if type(values) is not dict or tuple(values) != _PROJECTION_KEYS_IN_RUST_ORDER:
        raise SpotV7SemanticProofVerificationErrorV1(
            "Spot V7 authenticated projection schema mismatch"
        )
    _require_length_and_hash(
        request, values, length_key="request_bytes", hash_key="request_sha256", name="request"
    )
    _require_length_and_hash(
        v7_receipt,
        values,
        length_key="v7_receipt_bytes",
        hash_key="v7_receipt_sha256",
        name="V7 receipt",
    )
    _require_length_and_hash(
        guest_input,
        values,
        length_key="guest_input_bytes",
        hash_key="guest_input_sha256",
        name="guest input",
    )
    _require_length_and_hash(
        source_v6_receipt,
        values,
        length_key="source_v6_receipt_bytes",
        hash_key="source_v6_receipt_sha256",
        name="source V6 receipt",
    )
    verifier_output = _lower_hex_bytes(values, "verifier_output_hex")
    if len(verifier_output) > SPOT_V7_VERIFIER_PAYLOAD_CAP_BYTES_V1:
        raise SpotV7SemanticProofVerificationErrorV1("V7 verifier output exceeds its bound")
    _require_length_and_hash(
        verifier_output,
        values,
        length_key="verifier_output_bytes",
        hash_key="verifier_output_sha256",
        name="verifier output",
    )
    try:
        decoded = decode_structural_v7_verifier_payload_v1(verifier_output)
    except (SpotV7FirecrackerProtocolRejectV1, TypeError) as exc:
        raise SpotV7SemanticProofVerificationErrorV1(
            "Spot V7 verifier output fails exact structural decoding"
        ) from exc
    _require_length_and_hash(
        decoded.journal_bytes,
        values,
        length_key="journal_bytes",
        hash_key="journal_sha256",
        name="V7 journal",
    )
    _require_length_and_hash(
        decoded.plan_b_bytes,
        values,
        length_key="plan_b_bytes",
        hash_key="plan_b_sha256",
        name="Plan B",
    )
    raw_profile = values.get("receipt_security_profile")
    if type(raw_profile) is not dict or (tuple(raw_profile) != _RECEIPT_PROFILE_KEYS_IN_RUST_ORDER):
        raise SpotV7SemanticProofVerificationErrorV1(
            "receipt security profile field order mismatch"
        )
    profile = _parse_receipt_profile(raw_profile)
    projection = _projection_from_values(
        values,
        profile=profile,
        decoded=decoded,
        request=request,
        response=raw,
        v7_receipt=v7_receipt,
        guest_input=guest_input,
        source_v6_receipt=source_v6_receipt,
        verifier_output=verifier_output,
        authority_manifest_sha256=authority_manifest_sha256,
        executable_sha256=executable_sha256,
    )
    _require_policy_match(projection, policy)
    _require_payload_associations(projection, decoded)
    return projection


def _projection_from_values(
    values: Mapping[str, Any],
    *,
    profile: _ReceiptSecurityProfileV1,
    decoded: Any,
    request: bytes,
    response: bytes,
    v7_receipt: bytes,
    guest_input: bytes,
    source_v6_receipt: bytes,
    verifier_output: bytes,
    authority_manifest_sha256: str,
    executable_sha256: str,
) -> _PinnedSpotV7ProofProjectionDataV1:
    consumed = _hash_tuple(values, "consumed_object_ids")
    if len(consumed) > MAX_SPOT_V7_CONSUMED_OBJECTS_V1:
        raise SpotV7SemanticProofVerificationErrorV1("too many consumed object IDs")
    if consumed != tuple(sorted(consumed)) or len(set(consumed)) != len(consumed):
        raise SpotV7SemanticProofVerificationErrorV1(
            "consumed object IDs are not canonical and unique"
        )
    epoch_id = _strict_nonnegative_int(values, "epoch_id")
    if epoch_id > (1 << 64) - 1:
        raise SpotV7SemanticProofVerificationErrorV1("epoch_id exceeds u64")
    hash_values = {
        key: _mapping_hash(values, key)
        for key in (
            "verified_program_id",
            "verified_profile_id",
            "verified_program_manifest_root",
            "source_child_program_id",
            "required_source_child_receipt_security_profile_id",
            "source_child_claim_binding",
            "source_child_journal_sha256",
            "application_id",
            "chain_or_domain_id",
            "data_availability_certificate_root",
            "data_root",
            "settlement_effect_plan_commitment",
            "economic_action_id",
            "authorization_nullifier",
            "authorization_grant_spend_nullifier",
            "action_ids_root",
            "action_authorization_bindings_root",
            "authorization_grant_spends_root",
            "consumed_object_ids_root",
            "cell_transitions_root",
            "pre_state_root",
            "post_state_root",
        )
    }
    return _PinnedSpotV7ProofProjectionDataV1(
        **hash_values,
        epoch_id=epoch_id,
        receipt_security_profile=profile,
        consumed_object_ids=consumed,
        exact_v7_receipt_bytes=v7_receipt,
        exact_guest_input_bytes=guest_input,
        exact_source_v6_receipt_bytes=source_v6_receipt,
        exact_verifier_output_bytes=verifier_output,
        exact_v7_journal_bytes=decoded.journal_bytes,
        exact_plan_b_bytes=decoded.plan_b_bytes,
        proof_verifier_authority_manifest_sha256=authority_manifest_sha256,
        proof_verifier_executable_sha256=executable_sha256,
        proof_verification_request_sha256=hashlib.sha256(request).hexdigest(),
        proof_verification_response_sha256=hashlib.sha256(response).hexdigest(),
    )


def _require_policy_match(
    projection: _PinnedSpotV7ProofProjectionDataV1,
    policy: _TrustedSpotV7ProofPolicyV1,
) -> None:
    for name in (
        "application_id",
        "chain_or_domain_id",
        "epoch_id",
        "verified_program_id",
        "verified_profile_id",
        "verified_program_manifest_root",
        "receipt_security_profile",
        "source_child_program_id",
        "required_source_child_receipt_security_profile_id",
    ):
        if getattr(projection, name) != getattr(policy, name):
            raise SpotV7SemanticProofVerificationErrorV1(
                f"authenticated projection {name} does not match governed policy"
            )


def _require_payload_associations(
    projection: _PinnedSpotV7ProofProjectionDataV1,
    decoded: Any,
) -> None:
    output = decoded.fixed_fields
    journal = decoded.journal_fixed_fields
    binding = decoded.effect_binding_fixed_fields
    expected = (
        (projection.verified_program_id, output[0]),
        (projection.verified_profile_id, output[1]),
        (projection.verified_program_manifest_root, output[2]),
        (projection.source_child_program_id, output[4]),
        (projection.required_source_child_receipt_security_profile_id, output[5]),
        (projection.source_child_claim_binding, output[6]),
        (projection.source_child_journal_sha256, output[7]),
        (projection.data_availability_certificate_root, output[8]),
        (projection.data_root, output[9]),
        (projection.settlement_effect_plan_commitment, output[10]),
        (projection.pre_state_root, output[12]),
        (projection.post_state_root, output[13]),
        (projection.action_ids_root, output[14]),
        (projection.action_authorization_bindings_root, output[15]),
        (projection.authorization_grant_spends_root, output[16]),
        (projection.consumed_object_ids_root, output[17]),
        (projection.cell_transitions_root, binding[5]),
        (projection.pre_state_root, binding[6]),
        (projection.post_state_root, binding[7]),
        (projection.economic_action_id, binding[8]),
        (projection.settlement_effect_plan_commitment, journal[10]),
    )
    for actual, encoded in expected:
        if bytes.fromhex(actual) != encoded:
            raise SpotV7SemanticProofVerificationErrorV1(
                "authenticated projection disagrees with the exact verifier payload"
            )
    roots = (
        (
            projection.action_ids_root,
            _list_root(_ACTION_IDS_ROOT_DOMAIN_V1, (projection.economic_action_id,)),
        ),
        (
            projection.action_authorization_bindings_root,
            _list_root(
                _ACTION_BINDINGS_ROOT_DOMAIN_V1,
                (projection.authorization_nullifier,),
            ),
        ),
        (
            projection.authorization_grant_spends_root,
            _list_root(
                _GRANT_SPENDS_ROOT_DOMAIN_V1,
                (projection.authorization_grant_spend_nullifier,),
            ),
        ),
        (
            projection.consumed_object_ids_root,
            _list_root(_CONSUMED_OBJECTS_ROOT_DOMAIN_V1, projection.consumed_object_ids),
        ),
    )
    if any(actual != derived for actual, derived in roots):
        raise SpotV7SemanticProofVerificationErrorV1(
            "authenticated projection list roots do not match their exact members"
        )


def _validate_policy_fields(values: Mapping[str, object]) -> _TrustedSpotV7ProofPolicyV1:
    required = _AUTHORITY_KEYS - {"schema", "executable_sha256", "executable_format"}
    if not isinstance(values, Mapping) or set(values) != required:
        raise ValueError("Spot V7 proof verifier policy schema mismatch")
    hashes = {
        key: _mapping_hash(values, key)
        for key in (
            "application_id",
            "chain_or_domain_id",
            "verified_program_id",
            "verified_profile_id",
            "verified_program_manifest_root",
            "source_child_program_id",
            "required_source_child_receipt_security_profile_id",
        )
    }
    epoch_id = _strict_nonnegative_int(values, "epoch_id")
    if epoch_id > (1 << 64) - 1:
        raise ValueError("Spot V7 proof verifier policy epoch exceeds u64")
    return _TrustedSpotV7ProofPolicyV1(
        **hashes,
        epoch_id=epoch_id,
        receipt_security_profile=_parse_receipt_profile(values.get("receipt_security_profile")),
    )


def _policy_to_json(policy: _TrustedSpotV7ProofPolicyV1) -> dict[str, object]:
    return {
        "application_id": policy.application_id,
        "chain_or_domain_id": policy.chain_or_domain_id,
        "epoch_id": policy.epoch_id,
        "verified_program_id": policy.verified_program_id,
        "verified_profile_id": policy.verified_profile_id,
        "verified_program_manifest_root": policy.verified_program_manifest_root,
        "receipt_security_profile": {
            "profile_id": policy.receipt_security_profile.profile_id,
            "receipt_kind": policy.receipt_security_profile.receipt_kind,
            "verifier_parameters": policy.receipt_security_profile.verifier_parameters,
            "hashfn": policy.receipt_security_profile.hashfn,
            "control_id": policy.receipt_security_profile.control_id,
        },
        "source_child_program_id": policy.source_child_program_id,
        "required_source_child_receipt_security_profile_id": (
            policy.required_source_child_receipt_security_profile_id
        ),
    }


def _parse_receipt_profile(value: object) -> _ReceiptSecurityProfileV1:
    if type(value) is not dict or set(value) != _RECEIPT_PROFILE_KEYS:
        raise SpotV7SemanticProofVerificationErrorV1("receipt security profile schema mismatch")
    profile_id = _mapping_token(value, "profile_id")
    receipt_kind = _mapping_token(value, "receipt_kind")
    verifier_parameters = _mapping_hash(value, "verifier_parameters")
    hashfn = _mapping_token(value, "hashfn")
    control_id = _mapping_hash(value, "control_id")
    return _ReceiptSecurityProfileV1(
        profile_id,
        receipt_kind,
        verifier_parameters,
        hashfn,
        control_id,
    )


def _decode_strict_json_object(raw: bytes, name: str) -> dict[str, Any]:
    try:
        value = json.loads(
            raw,
            object_pairs_hook=_reject_duplicate_object_keys,
            parse_float=_reject_json_float,
            parse_constant=_reject_json_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, TypeError, ValueError) as exc:
        raise SpotV7SemanticProofVerificationErrorV1(f"Spot V7 {name} must be strict JSON") from exc
    if type(value) is not dict:
        raise SpotV7SemanticProofVerificationErrorV1(f"Spot V7 {name} must be one object")
    return value


def _reject_json_float(_value: str) -> NoReturn:
    raise ValueError("floating-point JSON values are forbidden")


def _rust_json_bytes(value: Mapping[str, object]) -> bytes:
    return json.dumps(value, ensure_ascii=True, separators=(",", ":")).encode("ascii")


def _require_exact_bytes(value: bytes, *, maximum: int, name: str) -> None:
    if type(value) is not bytes:
        raise TypeError(f"{name} must be exactly bytes")
    if not value or len(value) > maximum:
        raise SpotV7SemanticProofVerificationErrorV1(f"{name} byte length is out of bounds")


def _require_length_and_hash(
    raw: bytes,
    fields: Mapping[str, Any],
    *,
    length_key: str,
    hash_key: str,
    name: str,
) -> None:
    if _strict_nonnegative_int(fields, length_key) != len(raw):
        raise SpotV7SemanticProofVerificationErrorV1(f"{name} length mismatch")
    if _mapping_hash(fields, hash_key) != hashlib.sha256(raw).hexdigest():
        raise SpotV7SemanticProofVerificationErrorV1(f"{name} SHA-256 mismatch")


def _strict_nonnegative_int(values: Mapping[str, object], key: str) -> int:
    value = values.get(key)
    if type(value) is not int or value < 0:
        raise SpotV7SemanticProofVerificationErrorV1(f"{key} must be a nonnegative integer")
    return value


def _mapping_string(values: Mapping[str, object], key: str) -> str:
    value = values.get(key)
    if type(value) is not str:
        raise SpotV7SemanticProofVerificationErrorV1(f"{key} must be a string")
    return value


def _mapping_token(values: Mapping[str, object], key: str) -> str:
    value = _mapping_string(values, key)
    if not 1 <= len(value) <= 128 or not value.isascii():
        raise SpotV7SemanticProofVerificationErrorV1(f"{key} token is invalid")
    if any(
        character not in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789._:-"
        for character in value
    ):
        raise SpotV7SemanticProofVerificationErrorV1(f"{key} token is invalid")
    return value


def _mapping_hash(values: Mapping[str, object], key: str) -> str:
    value = _mapping_string(values, key)
    _require_bare_hash(value, key)
    return value


def _require_bare_hash(value: str, name: str) -> None:
    if (
        type(value) is not str
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise SpotV7SemanticProofVerificationErrorV1(f"{name} must be lowercase 64-character hex")
    if value == "00" * 32:
        raise SpotV7SemanticProofVerificationErrorV1(f"{name} must be nonzero")


def _lower_hex_bytes(values: Mapping[str, object], key: str) -> bytes:
    value = _mapping_string(values, key)
    if (
        not value
        or len(value) % 2
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise SpotV7SemanticProofVerificationErrorV1(f"{key} must be exact lowercase hex")
    try:
        return bytes.fromhex(value)
    except ValueError as exc:
        raise SpotV7SemanticProofVerificationErrorV1(f"{key} must be exact lowercase hex") from exc


def _hash_tuple(values: Mapping[str, object], key: str) -> tuple[str, ...]:
    raw = values.get(key)
    if type(raw) is not list:
        raise SpotV7SemanticProofVerificationErrorV1(f"{key} must be a list")
    result: list[str] = []
    for item in raw:
        if type(item) is not str:
            raise SpotV7SemanticProofVerificationErrorV1(f"{key} members must be strings")
        _require_bare_hash(item, f"{key} member")
        result.append(item)
    return tuple(result)


def _list_root(domain: bytes, values: tuple[str, ...]) -> str:
    hasher = hashlib.sha256()
    hasher.update(len(domain).to_bytes(2, "big"))
    hasher.update(domain)
    hasher.update(len(values).to_bytes(4, "big"))
    for value in values:
        hasher.update(bytes.fromhex(value))
    return hasher.hexdigest()
