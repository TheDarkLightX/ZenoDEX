"""Pinned verifier adapter for state-bound settlement-certificate admission.

The external verifier owns receipt decoding, image/profile checks, canonical
certificate decoding, and exact effect-plan reconstruction.  This adapter pins
that executable and one canonical policy manifest, executes it once, validates
its complete output shape, mints the private capability, and hands the value to
the atomic SQLite store.  Returned receipts remain non-authoritative until the
final settlement image and governed release policy are available.
"""

from __future__ import annotations

import hashlib
import json
import os
import resource
import subprocess
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, Any, Mapping, NoReturn, final

from src.core._zrpf_settlement_certificate_authority import (
    _AuthenticatedSettlementCertificateV1,
    _mint_authenticated_settlement_certificate_after_verification,
    _SettlementCertificateVerificationProvenanceV1,
    _VerifiedSettlementEpochCertificateV1,
)
from src.core.recursive_stark_admission import (
    RecursiveStarkRootFacts,
    TrustedRecursiveStarkAdmissionPolicy,
    _mint_recursive_stark_root_facts_after_verification,
    _RecursiveStarkVerificationProvenance,
    recursive_child_verification_claims_root_v1,
    recursive_message_ids_root_v1,
    recursive_receipt_ids_root_v1,
)
from src.core.zrpf_settlement_effect_plan import SettlementEffectPlanV1
from src.integration._zrpf_atomic_settlement_plan_codec import (
    _decode_canonical_settlement_plan_v1,
)
from src.integration.recursive_stark_verifier_adapter import (
    DEFAULT_VERIFIER_ADDRESS_SPACE_BYTES,
    DEFAULT_VERIFIER_STACK_BYTES,
    MAX_AUTHORITY_MANIFEST_BYTES,
    MAX_VERIFIER_REQUEST_BYTES,
    RecursiveStarkVerificationError,
    RecursiveVerifierExecutableFormat,
    _canonical_json_bytes,
    _communicate_bounded,
    _reject_duplicate_object_keys,
    _reject_json_constant,
    _sealed_executable_snapshot,
    _terminate_process_group,
    _verifier_environment,
)
from src.state.canonical import canonical_json_bytes

if TYPE_CHECKING:
    from src.integration.recursive_stark_admission_store_types import (
        DurableRecursiveStarkAdmissionCursor,
    )
    from src.integration.zrpf_atomic_settlement_store import (
        SQLiteZrpfAtomicSettlementStoreV1,
    )
    from src.integration.zrpf_atomic_settlement_store_types import (
        DurableZrpfSettlementCursorV1,
        DurableZrpfStateBoundSettlementResultV1,
    )

SETTLEMENT_AUTHORITY_MANIFEST_SCHEMA_V1 = (
    "zenodex.settlement_certificate_verifier_authority.v1"
)
VERIFIED_SETTLEMENT_CERTIFICATE_SCHEMA_V1 = (
    "zenodex.verified_settlement_epoch_certificate.v1"
)
_NON_RELEASE_POLICY_BINDING_DOMAIN_V1 = (
    b"zenodex.zrpf.non_release_settlement_admission_policy_binding.v1"
)

_TRUSTED_EXPECTATION_KEYS = frozenset(
    {
        "application_id",
        "chain_id",
        "chain_or_domain_id",
        "epoch_id",
        "proof_profile",
        "public_policy_hash",
        "receipt_codec",
        "receipt_control_id",
        "receipt_hashfn",
        "receipt_kind",
        "receipt_verifier_parameters",
        "settlement_image_id",
        "settlement_manifest_sha256",
        "settlement_profile_id",
        "verifier_set_root",
    }
)

_VERIFIED_CERTIFICATE_KEYS = frozenset(
    {
        "schema",
        "certificate_version",
        "application_id",
        "chain_id",
        "chain_or_domain_id",
        "epoch_id",
        "proof_profile",
        "public_policy_hash",
        "verifier_set_root",
        "receipt_codec",
        "receipt_control_id",
        "receipt_hashfn",
        "receipt_kind",
        "receipt_verifier_parameters",
        "settlement_image_id",
        "settlement_manifest_sha256",
        "settlement_profile_id",
        "semantic_root_journal_hash",
        "semantic_claim_hash",
        "certificate_journal_hash",
        "settlement_claim_hash",
        "settlement_receipt_id",
        "pre_state_root",
        "post_state_root",
        "economic_action_ids_root",
        "ledger_cell_writes_root",
        "asset_effects_root",
        "proof_tree_root",
        "dependency_manifest_root",
        "data_availability_certificate_root",
        "schedule_certificate_root",
        "carry_continuity_certificate_root",
        "action_authorization_bindings_root",
        "authorization_grant_spend_nullifiers_root",
        "consumed_object_ids_root",
        "message_effects_root",
        "carry_effects_root",
        "reward_effects_root",
        "effect_plan_commitment",
        "canonical_certificate_hex",
        "canonical_certificate_sha256",
        "exact_effect_plan_hex",
        "exact_effect_plan_sha256",
        "source_opened_replay_hex",
        "source_opened_replay_sha256",
        "data_availability_certificate_hex",
        "data_availability_certificate_sha256",
        "action_nullifiers",
        "consumed_object_ids",
        "authorization_grant_spend_nullifiers",
        "normalized_effect_plan",
    }
)


class SettlementCertificateVerificationError(ValueError):
    """Stable fail-closed error at the pinned settlement verifier boundary."""


@final
@dataclass(frozen=True)
class PinnedSettlementCertificateVerifierV1:
    """One executable and one replaceable canonical settlement-policy seam."""

    executable: Path
    authority_manifest_json: bytes
    authority_manifest_sha256: str
    timeout_seconds: int = 60
    max_address_space_bytes: int = DEFAULT_VERIFIER_ADDRESS_SPACE_BYTES
    max_stack_bytes: int = DEFAULT_VERIFIER_STACK_BYTES
    sha256: str = field(init=False)
    executable_format: RecursiveVerifierExecutableFormat = field(init=False)
    trusted_expectations: Mapping[str, Any] = field(init=False)
    _trusted_expectations_json: bytes = field(init=False, repr=False)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("PinnedSettlementCertificateVerifierV1 cannot be subclassed")

    def __post_init__(self) -> None:
        if not isinstance(self.executable, Path) or not self.executable.is_absolute():
            raise ValueError("settlement verifier executable must be an absolute pathlib.Path")
        _require_bare_sha256(
            self.authority_manifest_sha256,
            name="settlement verifier authority_manifest_sha256",
        )
        if type(self.timeout_seconds) is not int or not 1 <= self.timeout_seconds <= 300:
            raise ValueError("settlement verifier timeout_seconds must be in 1..300")
        if self.max_address_space_bytes < 256 * 1024 * 1024:
            raise ValueError("settlement verifier address-space limit is too small")
        if self.max_stack_bytes < 1024 * 1024:
            raise ValueError("settlement verifier stack limit is too small")
        executable_sha256, executable_format, expectations = _parse_authority_manifest_v1(
            self.authority_manifest_json,
            expected_sha256=self.authority_manifest_sha256,
        )
        object.__setattr__(self, "sha256", executable_sha256)
        object.__setattr__(self, "executable_format", executable_format)
        object.__setattr__(self, "trusted_expectations", json.loads(expectations))
        object.__setattr__(self, "_trusted_expectations_json", expectations)

    def verify_and_commit(
        self,
        *,
        store: SQLiteZrpfAtomicSettlementStoreV1,
        expected_admission_cursor: DurableRecursiveStarkAdmissionCursor,
        expected_settlement_cursor: DurableZrpfSettlementCursorV1,
        receipt: Mapping[str, Any],
        settlement_input: Mapping[str, Any],
    ) -> DurableZrpfStateBoundSettlementResultV1:
        """Verify exactly once, then atomically admit the sealed certificate."""

        from src.integration.recursive_stark_admission_store_types import (
            DurableRecursiveStarkAdmissionCursor,
        )
        from src.integration.zrpf_atomic_settlement_store import (
            SQLiteZrpfAtomicSettlementStoreV1,
        )
        from src.integration.zrpf_atomic_settlement_store_types import (
            DurableZrpfSettlementCursorV1,
        )

        if type(store) is not SQLiteZrpfAtomicSettlementStoreV1:
            raise TypeError("store must be exactly SQLiteZrpfAtomicSettlementStoreV1")
        if type(expected_admission_cursor) is not DurableRecursiveStarkAdmissionCursor:
            raise TypeError("expected_admission_cursor must be a durable admission cursor")
        if type(expected_settlement_cursor) is not DurableZrpfSettlementCursorV1:
            raise TypeError("expected_settlement_cursor must be a durable settlement cursor")
        if self.executable_format is not RecursiveVerifierExecutableFormat.STATIC_ELF_X86_64:
            raise SettlementCertificateVerificationError(
                "durable settlement admission requires a static ELF verifier"
            )
        authenticated = self._verify_authenticated_certificate(
            receipt=receipt,
            settlement_input=settlement_input,
        )
        return store._commit_authenticated_certificate(
            expected_admission_cursor=expected_admission_cursor,
            expected_settlement_cursor=expected_settlement_cursor,
            authenticated_certificate=authenticated,
        )

    def _verify_authenticated_certificate(
        self,
        *,
        receipt: Mapping[str, Any],
        settlement_input: Mapping[str, Any],
    ) -> _AuthenticatedSettlementCertificateV1:
        expectations = json.loads(self._trusted_expectations_json)
        request = {
            "schema": "zenodex.settlement_certificate_verify_request.v1",
            "receipt": _canonical_mapping_copy(receipt, "settlement receipt"),
            "settlement_input": _canonical_mapping_copy(
                settlement_input,
                "settlement verifier input",
            ),
            "trusted_expectations": expectations,
        }
        request_bytes = _bounded_canonical_json_bytes(request, "settlement verification request")
        request_sha256 = hashlib.sha256(request_bytes).hexdigest()
        stdout = self._execute_verifier_once(request_bytes)
        try:
            response = json.loads(
                stdout,
                object_pairs_hook=_reject_duplicate_object_keys,
                parse_constant=_reject_json_constant,
            )
        except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
            raise SettlementCertificateVerificationError(
                "settlement verifier stdout must be one JSON object"
            ) from exc
        certificate, plan = _parse_verified_certificate_response(
            response,
            trusted_expectations=expectations,
        )
        try:
            root_facts = _recursive_facts_from_certificate(certificate, plan, expectations)
        except (TypeError, ValueError) as exc:
            raise SettlementCertificateVerificationError(
                "verified settlement certificate identity binding is invalid"
            ) from exc
        admission_policy_binding_sha256 = hashlib.sha256(
            _NON_RELEASE_POLICY_BINDING_DOMAIN_V1
            + bytes.fromhex(self.authority_manifest_sha256)
        ).hexdigest()
        recursive_policy = TrustedRecursiveStarkAdmissionPolicy(
            expected_chain_id=_expectation_str(expectations, "chain_id"),
            expected_epoch_id=_expectation_int(expectations, "epoch_id"),
            expected_proof_profile=_expectation_str(expectations, "proof_profile"),
            expected_verifier_set_root=_prefixed_hash(
                _expectation_str(expectations, "verifier_set_root")
            ),
            expected_public_policy_hash=_prefixed_hash(
                _expectation_str(expectations, "public_policy_hash")
            ),
        )
        recursive_provenance = _RecursiveStarkVerificationProvenance(
            authority_manifest_sha256=self.authority_manifest_sha256,
            verifier_executable_sha256=self.sha256,
            verification_request_sha256=request_sha256,
            # The reused identity schema requires a binding digest. This
            # domain-separated value explicitly denotes a non-release policy.
            release_binding_config_digest="0x" + admission_policy_binding_sha256,
            replay_manifest_sha256="sha256:" + certificate.settlement_manifest_sha256,
        )
        try:
            authenticated_root = _mint_recursive_stark_root_facts_after_verification(
                root_facts,
                recursive_policy,
                recursive_provenance,
            )
            provenance = _SettlementCertificateVerificationProvenanceV1(
                authority_manifest_sha256=self.authority_manifest_sha256,
                verifier_executable_sha256=self.sha256,
                verification_request_sha256=request_sha256,
                admission_policy_binding_sha256=admission_policy_binding_sha256,
            )
            return _mint_authenticated_settlement_certificate_after_verification(
                authenticated_root,
                certificate,
                plan,
                provenance,
            )
        except (TypeError, ValueError) as exc:
            raise SettlementCertificateVerificationError(
                "verified settlement certificate capability binding is invalid"
            ) from exc

    def _execute_verifier_once(self, request_bytes: bytes) -> bytes:
        executable_fd: int | None = None
        try:
            executable_fd, actual_hash = _sealed_executable_snapshot(
                self.executable,
                executable_format=self.executable_format,
            )
            if actual_hash != self.sha256:
                raise SettlementCertificateVerificationError(
                    "settlement verifier binary hash mismatch"
                )
            process = subprocess.Popen(
                [f"/proc/self/fd/{executable_fd}"],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                start_new_session=True,
                pass_fds=(executable_fd,),
                cwd="/",
                env=_verifier_environment(),
            )
            try:
                self._apply_resource_limits(process.pid)
            except (OSError, ValueError) as exc:
                _terminate_process_group(process)
                raise SettlementCertificateVerificationError(
                    f"failed to apply settlement verifier resource limits: {exc}"
                ) from exc
            stdout, _stderr, returncode = _communicate_bounded(
                process,
                request_bytes=request_bytes,
                timeout_seconds=self.timeout_seconds,
            )
        except subprocess.TimeoutExpired as exc:
            raise SettlementCertificateVerificationError("settlement verifier timed out") from exc
        except RecursiveStarkVerificationError as exc:
            raise SettlementCertificateVerificationError(str(exc)) from exc
        except OSError as exc:
            raise SettlementCertificateVerificationError(
                f"settlement verifier process failed: {exc}"
            ) from exc
        finally:
            if executable_fd is not None:
                os.close(executable_fd)
        if returncode != 0:
            raise SettlementCertificateVerificationError(
                f"settlement verifier exited with status {returncode}"
            )
        return stdout

    def _apply_resource_limits(self, process_id: int) -> None:
        resource.prlimit(
            process_id,
            resource.RLIMIT_AS,
            (self.max_address_space_bytes, self.max_address_space_bytes),
        )
        resource.prlimit(
            process_id,
            resource.RLIMIT_STACK,
            (self.max_stack_bytes, self.max_stack_bytes),
        )
        cpu_seconds = self.timeout_seconds + 1
        resource.prlimit(process_id, resource.RLIMIT_CPU, (cpu_seconds, cpu_seconds))
        resource.prlimit(process_id, resource.RLIMIT_CORE, (0, 0))
        resource.prlimit(process_id, resource.RLIMIT_FSIZE, (0, 0))
        resource.prlimit(process_id, resource.RLIMIT_NOFILE, (32, 32))
        resource.prlimit(process_id, resource.RLIMIT_NPROC, (1, 1))


def settlement_certificate_authority_manifest_bytes_v1(
    *,
    executable_sha256: str,
    trusted_expectations: Mapping[str, Any],
    executable_format: RecursiveVerifierExecutableFormat = (
        RecursiveVerifierExecutableFormat.STATIC_ELF_X86_64
    ),
) -> bytes:
    """Build the canonical replaceable policy manifest for one verifier."""

    _require_bare_sha256(executable_sha256, name="settlement verifier sha256")
    if type(executable_format) is not RecursiveVerifierExecutableFormat:
        raise ValueError("settlement verifier executable_format unsupported")
    expectations = _canonical_mapping_copy(trusted_expectations, "trusted expectations")
    _validate_trusted_expectations(expectations)
    raw = _canonical_json_bytes(
        {
            "schema": SETTLEMENT_AUTHORITY_MANIFEST_SCHEMA_V1,
            "executable_sha256": executable_sha256,
            "executable_format": executable_format.value,
            "trusted_expectations": expectations,
        }
    )
    if len(raw) > MAX_AUTHORITY_MANIFEST_BYTES:
        raise ValueError("settlement verifier authority manifest exceeds byte limit")
    return raw


def _parse_authority_manifest_v1(
    raw: bytes,
    *,
    expected_sha256: str,
) -> tuple[str, RecursiveVerifierExecutableFormat, bytes]:
    if type(raw) is not bytes or not raw or len(raw) > MAX_AUTHORITY_MANIFEST_BYTES:
        raise ValueError("settlement verifier authority manifest byte length is invalid")
    if hashlib.sha256(raw).hexdigest() != expected_sha256:
        raise ValueError("settlement verifier authority manifest hash mismatch")
    try:
        value = json.loads(
            raw.decode("ascii"),
            object_pairs_hook=_reject_duplicate_object_keys,
            parse_float=_reject_json_float,
            parse_constant=_reject_json_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        raise ValueError("settlement verifier authority manifest must be canonical JSON") from exc
    if type(value) is not dict or set(value) != {
        "schema",
        "executable_sha256",
        "executable_format",
        "trusted_expectations",
    }:
        raise ValueError("settlement verifier authority manifest schema mismatch")
    if value["schema"] != SETTLEMENT_AUTHORITY_MANIFEST_SCHEMA_V1:
        raise ValueError("settlement verifier authority manifest schema mismatch")
    if _canonical_json_bytes(value) != raw:
        raise ValueError("settlement verifier authority manifest must be canonical JSON")
    executable_sha256 = value["executable_sha256"]
    _require_bare_sha256(executable_sha256, name="manifest executable_sha256")
    try:
        executable_format = RecursiveVerifierExecutableFormat(value["executable_format"])
    except (TypeError, ValueError) as exc:
        raise ValueError("settlement verifier executable_format unsupported") from exc
    expectations = _mapping(value["trusted_expectations"], "trusted_expectations")
    _validate_trusted_expectations(expectations)
    canonical_expectations = _canonical_json_bytes(expectations)
    return executable_sha256, executable_format, canonical_expectations


def _validate_trusted_expectations(value: Mapping[str, Any]) -> None:
    if set(value) != _TRUSTED_EXPECTATION_KEYS:
        raise ValueError("settlement verifier trusted expectations schema mismatch")
    for key in (
        "application_id",
        "chain_or_domain_id",
        "public_policy_hash",
        "receipt_control_id",
        "receipt_verifier_parameters",
        "settlement_image_id",
        "verifier_set_root",
    ):
        _prefixed_hash(_expectation_str(value, key))
    for key in (
        "chain_id",
        "proof_profile",
        "receipt_codec",
        "receipt_hashfn",
        "receipt_kind",
        "settlement_profile_id",
    ):
        _require_token(_expectation_str(value, key), name=f"trusted_expectations.{key}")
    _require_bare_sha256(
        _expectation_str(value, "settlement_manifest_sha256"),
        name="trusted_expectations.settlement_manifest_sha256",
    )
    epoch = _expectation_int(value, "epoch_id")
    if not 0 <= epoch <= (1 << 64) - 1:
        raise ValueError("trusted_expectations.epoch_id is out of bounds")


def _parse_verified_certificate_response(
    payload: object,
    *,
    trusted_expectations: Mapping[str, Any],
) -> tuple[_VerifiedSettlementEpochCertificateV1, SettlementEffectPlanV1]:
    response = _mapping(payload, "settlement verifier response")
    if set(response) != {"ok", "verified_settlement_certificate"} or response.get("ok") is not True:
        raise SettlementCertificateVerificationError(
            "settlement verifier response schema or acceptance mismatch"
        )
    values = _mapping(
        response.get("verified_settlement_certificate"),
        "verified_settlement_certificate",
    )
    if set(values) != _VERIFIED_CERTIFICATE_KEYS:
        raise SettlementCertificateVerificationError(
            "verified settlement certificate schema mismatch"
        )
    if values.get("schema") != VERIFIED_SETTLEMENT_CERTIFICATE_SCHEMA_V1:
        raise SettlementCertificateVerificationError(
            "verified settlement certificate schema unsupported"
        )
    _require_trusted_response_bindings(values, trusted_expectations)
    normalized = values.get("normalized_effect_plan")
    if type(normalized) is not dict:
        raise SettlementCertificateVerificationError(
            "normalized_effect_plan must be one canonical JSON object"
        )
    try:
        plan = _decode_canonical_settlement_plan_v1(canonical_json_bytes(normalized))
    except ValueError as exc:
        raise SettlementCertificateVerificationError(
            "normalized_effect_plan fails canonical V1 validation"
        ) from exc
    return _verified_certificate_from_values(values), plan


def _require_trusted_response_bindings(
    values: Mapping[str, Any],
    trusted_expectations: Mapping[str, Any],
) -> None:
    hash_keys = {
        "application_id",
        "chain_or_domain_id",
        "public_policy_hash",
        "receipt_control_id",
        "receipt_verifier_parameters",
        "settlement_image_id",
        "verifier_set_root",
    }
    for key in _TRUSTED_EXPECTATION_KEYS:
        observed = values.get(key)
        expected = trusted_expectations.get(key)
        if key in hash_keys:
            if not isinstance(observed, str) or not isinstance(expected, str):
                raise SettlementCertificateVerificationError(
                    f"verified settlement {key} must be a hash"
                )
            if _prefixed_hash(observed) != _prefixed_hash(expected):
                raise SettlementCertificateVerificationError(
                    f"verified settlement {key} trusted expectation mismatch"
                )
        elif observed != expected:
            raise SettlementCertificateVerificationError(
                f"verified settlement {key} trusted expectation mismatch"
            )


def _verified_certificate_from_values(
    values: Mapping[str, Any],
) -> _VerifiedSettlementEpochCertificateV1:
    try:
        return _VerifiedSettlementEpochCertificateV1(
            certificate_version=_int(values, "certificate_version"),
            application_id=_hash(values, "application_id"),
            chain_or_domain_id=_hash(values, "chain_or_domain_id"),
            epoch_id=_int(values, "epoch_id"),
            public_policy_hash=_hash(values, "public_policy_hash"),
            semantic_root_journal_hash=_hash(values, "semantic_root_journal_hash"),
            semantic_claim_hash=_hash(values, "semantic_claim_hash"),
            certificate_journal_hash=_hash(values, "certificate_journal_hash"),
            settlement_claim_hash=_hash(values, "settlement_claim_hash"),
            settlement_receipt_id=_hash(values, "settlement_receipt_id"),
            settlement_image_id=_hash(values, "settlement_image_id"),
            settlement_profile_id=_str(values, "settlement_profile_id"),
            settlement_manifest_sha256=_str(values, "settlement_manifest_sha256"),
            pre_state_root=_hash(values, "pre_state_root"),
            post_state_root=_hash(values, "post_state_root"),
            economic_action_ids_root=_hash(values, "economic_action_ids_root"),
            ledger_cell_writes_root=_hash(values, "ledger_cell_writes_root"),
            asset_effects_root=_hash(values, "asset_effects_root"),
            proof_tree_root=_hash(values, "proof_tree_root"),
            dependency_manifest_root=_hash(values, "dependency_manifest_root"),
            data_availability_certificate_root=_hash(
                values,
                "data_availability_certificate_root",
            ),
            schedule_certificate_root=_hash(values, "schedule_certificate_root"),
            carry_continuity_certificate_root=_hash(
                values,
                "carry_continuity_certificate_root",
            ),
            action_authorization_bindings_root=_hash(
                values,
                "action_authorization_bindings_root",
            ),
            authorization_grant_spend_nullifiers_root=_hash(
                values,
                "authorization_grant_spend_nullifiers_root",
            ),
            consumed_object_ids_root=_hash(values, "consumed_object_ids_root"),
            message_effects_root=_hash(values, "message_effects_root"),
            carry_effects_root=_hash(values, "carry_effects_root"),
            reward_effects_root=_hash(values, "reward_effects_root"),
            effect_plan_commitment=_hash(values, "effect_plan_commitment"),
            canonical_certificate=_hex_bytes(values, "canonical_certificate_hex"),
            canonical_certificate_sha256=_str(values, "canonical_certificate_sha256"),
            exact_effect_plan=_hex_bytes(values, "exact_effect_plan_hex"),
            exact_effect_plan_sha256=_str(values, "exact_effect_plan_sha256"),
            source_opened_replay=_hex_bytes(values, "source_opened_replay_hex"),
            source_opened_replay_sha256=_str(values, "source_opened_replay_sha256"),
            data_availability_certificate=_hex_bytes(
                values,
                "data_availability_certificate_hex",
            ),
            data_availability_certificate_sha256=_str(
                values,
                "data_availability_certificate_sha256",
            ),
            action_nullifiers=_hash_tuple(values, "action_nullifiers"),
            consumed_object_ids=_hash_tuple(values, "consumed_object_ids"),
            authorization_grant_spend_nullifiers=_hash_tuple(
                values,
                "authorization_grant_spend_nullifiers",
            ),
        )
    except (TypeError, ValueError) as exc:
        raise SettlementCertificateVerificationError(
            "verified settlement certificate facts are invalid"
        ) from exc


def _recursive_facts_from_certificate(
    certificate: _VerifiedSettlementEpochCertificateV1,
    plan: SettlementEffectPlanV1,
    expectations: Mapping[str, Any],
) -> RecursiveStarkRootFacts:
    claims = (certificate.semantic_claim_hash, certificate.settlement_claim_hash)
    receipts = (certificate.settlement_receipt_id,)
    messages = tuple(row.message_id for row in plan.message_effects)
    return RecursiveStarkRootFacts(
        chain_id=_expectation_str(expectations, "chain_id"),
        epoch_id=certificate.epoch_id,
        proof_profile=_expectation_str(expectations, "proof_profile"),
        root_journal_hash=certificate.semantic_root_journal_hash,
        verifier_set_root=_prefixed_hash(_expectation_str(expectations, "verifier_set_root")),
        public_policy_hash=certificate.public_policy_hash,
        child_verification_claim_hashes=claims,
        child_verification_claims_root=recursive_child_verification_claims_root_v1(claims),
        accepted_receipt_ids=receipts,
        accepted_receipts_root=recursive_receipt_ids_root_v1(receipts),
        cross_shard_message_ids=messages,
        cross_shard_message_ids_root=recursive_message_ids_root_v1(messages),
    )


def _canonical_mapping_copy(value: Mapping[str, Any], name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise SettlementCertificateVerificationError(f"{name} must be an object")
    try:
        encoded = _bounded_canonical_json_bytes(value, name)
        copied = json.loads(encoded)
    except (TypeError, ValueError, json.JSONDecodeError, RecursionError) as exc:
        raise SettlementCertificateVerificationError(f"{name} must be canonical JSON") from exc
    if type(copied) is not dict:
        raise SettlementCertificateVerificationError(f"{name} must be an object")
    return copied


def _bounded_canonical_json_bytes(value: object, name: str) -> bytes:
    try:
        raw = _canonical_json_bytes(value)
    except (TypeError, ValueError, RecursionError) as exc:
        raise SettlementCertificateVerificationError(f"{name} must be canonical JSON") from exc
    if len(raw) > MAX_VERIFIER_REQUEST_BYTES:
        raise SettlementCertificateVerificationError(f"{name} exceeds byte limit")
    return raw


def _mapping(value: object, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise SettlementCertificateVerificationError(f"{name} must be an object")
    return value


def _str(values: Mapping[str, Any], key: str) -> str:
    value = values.get(key)
    if type(value) is not str:
        raise SettlementCertificateVerificationError(f"verified settlement {key} must be a string")
    return value


def _int(values: Mapping[str, Any], key: str) -> int:
    value = values.get(key)
    if type(value) is not int:
        raise SettlementCertificateVerificationError(f"verified settlement {key} must be an int")
    return value


def _hash(values: Mapping[str, Any], key: str) -> str:
    return _prefixed_hash(_str(values, key))


def _hash_tuple(values: Mapping[str, Any], key: str) -> tuple[str, ...]:
    value = values.get(key)
    if type(value) is not list:
        raise SettlementCertificateVerificationError(
            f"verified settlement {key} must be a hash list"
        )
    return tuple(_prefixed_hash(item) for item in value)


def _hex_bytes(values: Mapping[str, Any], key: str) -> bytes:
    value = _str(values, key)
    if not value or len(value) % 2 or any(char not in "0123456789abcdef" for char in value):
        raise SettlementCertificateVerificationError(
            f"verified settlement {key} must be nonempty lowercase even-length hex"
        )
    return bytes.fromhex(value)


def _prefixed_hash(value: object) -> str:
    if type(value) is not str:
        raise SettlementCertificateVerificationError("hash must be a string")
    bare = value.removeprefix("0x")
    if len(bare) != 64 or any(char not in "0123456789abcdef" for char in bare):
        raise SettlementCertificateVerificationError("hash must be lowercase 32-byte hex")
    if bare == "00" * 32:
        raise SettlementCertificateVerificationError("hash must be nonzero")
    return "0x" + bare


def _expectation_str(values: Mapping[str, Any], key: str) -> str:
    value = values.get(key)
    if type(value) is not str:
        raise SettlementCertificateVerificationError(
            f"trusted_expectations.{key} must be a string"
        )
    return value


def _expectation_int(values: Mapping[str, Any], key: str) -> int:
    value = values.get(key)
    if type(value) is not int:
        raise SettlementCertificateVerificationError(
            f"trusted_expectations.{key} must be an int"
        )
    return value


def _require_token(value: str, *, name: str) -> None:
    if not value or len(value.encode("ascii", errors="strict")) > 128:
        raise ValueError(f"{name} must be a bounded ASCII token")
    allowed = frozenset("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789._:-")
    if any(char not in allowed for char in value):
        raise ValueError(f"{name} must use canonical token characters")


def _require_bare_sha256(value: object, *, name: str) -> None:
    if type(value) is not str or len(value) != 64:
        raise ValueError(f"{name} must be lowercase 64-character hex")
    if any(char not in "0123456789abcdef" for char in value):
        raise ValueError(f"{name} must be lowercase 64-character hex")


def _reject_json_float(value: str) -> NoReturn:
    raise ValueError(f"authority manifest float is forbidden: {value}")


__all__ = [
    "PinnedSettlementCertificateVerifierV1",
    "SETTLEMENT_AUTHORITY_MANIFEST_SCHEMA_V1",
    "SettlementCertificateVerificationError",
    "settlement_certificate_authority_manifest_bytes_v1",
]
