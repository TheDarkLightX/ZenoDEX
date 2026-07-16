"""Pinned Rust cross-checker for authenticated Spot V7 checkpoint finality.

The protocol-specific ZenoLedger adapter authenticates BLS quorum evidence.
This adapter independently reconstructs the proof-neutral V2 policy request,
executes one manifest-pinned static checker, and seals the exact BLS transition
with that invocation evidence.  The result remains authority-false until the
remaining release, runtime, DA, and atomic-settlement gates are satisfied.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import NoReturn, SupportsIndex, cast, final

from src.integration._zeno_ledger_pinned_verifier_process_v1 import (
    PinnedVerifierProcessError,
    VerifierExecutableFormatV1,
    execute_pinned_verifier_once,
)
from src.integration._zrpf_spot_v7_checkpoint_finality_checker_codec import (
    CHECKPOINT_FINALITY_CHECKER_PROTOCOL_VERSION_V1,
    CHECKPOINT_FINALITY_CHECKER_REQUEST_SCHEMA_V1,
    CHECKPOINT_FINALITY_CHECKER_RESPONSE_SCHEMA_V1,
    RESPONSE_BYTES_V1,
    _CheckpointFinalityCheckerBindingV1,
    _CheckpointFinalityCheckerInputV1,
    _CheckpointFinalityCheckerPolicyV1,
    _encode_checker_request_v1,
    _expected_response_v1,
    _parse_checker_response_v1,
)
from src.integration._zrpf_spot_v7_operational_policy_v3 import (
    _GovernedSpotV7OperationalPolicyV3,
    _require_governed_operational_policy_v3,
)
from src.integration.recursive_stark_verifier_adapter import (
    DEFAULT_VERIFIER_ADDRESS_SPACE_BYTES,
    DEFAULT_VERIFIER_STACK_BYTES,
    _reject_duplicate_object_keys,
    _reject_json_constant,
)
from src.integration.zrpf_spot_v7_zeno_ledger_finality_adapter import (
    _AuthenticatedExactCheckpointFinalityTransitionV3,
)
from src.state.canonical import canonical_json_bytes

CHECKPOINT_FINALITY_CHECKER_AUTHORITY_SCHEMA_V1 = (
    "zenodex.zrpf.checkpoint_finality_checker_authority.v1"
)
_MAX_AUTHORITY_MANIFEST_BYTES_V1 = 4_096
_MAX_CHECKER_STDERR_BYTES_V1 = 4_096
_MANIFEST_KEYS_V1 = frozenset(
    {
        "schema",
        "checker_protocol_version",
        "request_schema",
        "response_schema",
        "executable_sha256",
        "executable_format",
        "release_authority",
        "settlement_authority",
        "production_authority",
    }
)


class CheckpointFinalityCheckerAdapterRejectV1(str, Enum):
    AUTHORITY_MANIFEST_INVALID = "authority_manifest_invalid"
    AUTHENTICATED_INPUT_INVALID = "authenticated_input_invalid"
    CHECKER_REJECTED = "checker_rejected"
    CHECKER_RESPONSE_INVALID = "checker_response_invalid"
    SEALED_RESULT_INVALID = "sealed_result_invalid"


class CheckpointFinalityCheckerAdapterRejectedV1(ValueError):
    """Stable fail-closed rejection at the BLS-to-Rust checker boundary."""

    def __init__(self, reason: CheckpointFinalityCheckerAdapterRejectV1, detail: str) -> None:
        self.reason = reason
        self.detail = detail
        super().__init__(f"{reason.value}: {detail}")


@dataclass(frozen=True, slots=True)
class _CheckpointFinalityCheckerInvocationEvidenceV1:
    authority_manifest_sha256: str
    executable_sha256: str
    request_sha256: str
    response_sha256: str

    def __post_init__(self) -> None:
        for name in (
            "authority_manifest_sha256",
            "executable_sha256",
            "request_sha256",
            "response_sha256",
        ):
            _require_bare_sha256(getattr(self, name), name.replace("_", " "))


@dataclass(frozen=True, slots=True)
class _CheckpointFinalityCheckerInvocationArtifactsV1:
    """Exact live invocation artifacts retained by the operational packet."""

    exact_authority_manifest_bytes: bytes
    exact_request_bytes: bytes
    exact_response_bytes: bytes
    evidence: _CheckpointFinalityCheckerInvocationEvidenceV1

    def __post_init__(self) -> None:
        if type(self.exact_authority_manifest_bytes) is not bytes:
            raise TypeError("checkpoint-finality authority manifest must be exact bytes")
        if type(self.exact_request_bytes) is not bytes or not self.exact_request_bytes:
            raise TypeError("checkpoint-finality request must be nonempty exact bytes")
        if type(self.exact_response_bytes) is not bytes:
            raise TypeError("checkpoint-finality response must be exact bytes")
        if type(self.evidence) is not _CheckpointFinalityCheckerInvocationEvidenceV1:
            raise TypeError("checkpoint-finality invocation evidence has the wrong type")
        _revalidate_invocation_artifacts_v1(self)


@final
class _CrossCheckedAuthenticatedCheckpointFinalityTransitionV1:
    """Non-transferable BLS result cross-checked by one pinned Rust invocation."""

    __slots__ = (
        "_evidence",
        "_exact_authority_manifest_bytes",
        "_exact_request_bytes",
        "_exact_response_bytes",
        "_finality",
        "_policy",
        "_seal",
    )

    _policy: _GovernedSpotV7OperationalPolicyV3
    _finality: _AuthenticatedExactCheckpointFinalityTransitionV3
    _evidence: _CheckpointFinalityCheckerInvocationEvidenceV1
    _exact_authority_manifest_bytes: bytes
    _exact_request_bytes: bytes
    _exact_response_bytes: bytes
    _seal: object

    def __new__(
        cls,
    ) -> _CrossCheckedAuthenticatedCheckpointFinalityTransitionV1:
        raise TypeError("cross-checked checkpoint finality requires exact checker execution")

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("cross-checked checkpoint finality cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("cross-checked checkpoint finality cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("cross-checked checkpoint finality cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("cross-checked checkpoint finality cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("cross-checked checkpoint finality cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("cross-checked checkpoint finality cannot be serialized")

    def _has_private_seal(self) -> bool:
        return getattr(self, "_seal", None) is self

    def _finality_for_operational_join_v3(
        self,
        policy: object,
    ) -> _AuthenticatedExactCheckpointFinalityTransitionV3:
        if policy is not self._policy:
            raise ValueError("cross-checked finality retains a different governed policy")
        _revalidate_cross_checked_transition_v1(self)
        return self._finality

    def _invocation_artifacts_for_operational_join_v3(
        self,
        policy: object,
    ) -> _CheckpointFinalityCheckerInvocationArtifactsV1:
        if policy is not self._policy:
            raise ValueError("cross-checked finality retains a different governed policy")
        _revalidate_cross_checked_transition_v1(self)
        return _CheckpointFinalityCheckerInvocationArtifactsV1(
            exact_authority_manifest_bytes=self._exact_authority_manifest_bytes,
            exact_request_bytes=self._exact_request_bytes,
            exact_response_bytes=self._exact_response_bytes,
            evidence=self._evidence,
        )

    @property
    def cryptographic_checkpoint_quorum_supported(self) -> bool:
        return True

    @property
    def manifest_pinned_checker_cross_check_executed(self) -> bool:
        _revalidate_cross_checked_transition_v1(self)
        return True

    @property
    def release_governed_checker_identity_verified(self) -> bool:
        return False

    @property
    def hostile_same_interpreter_resistance_established(self) -> bool:
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


@final
@dataclass(frozen=True, slots=True)
class PinnedSpotV7CheckpointFinalityCheckerV1:
    """One manifest-pinned proof-neutral checker; release selection is external."""

    executable: Path
    authority_manifest_json: bytes
    authority_manifest_sha256: str
    timeout_seconds: int = 30
    max_address_space_bytes: int = DEFAULT_VERIFIER_ADDRESS_SPACE_BYTES
    max_stack_bytes: int = DEFAULT_VERIFIER_STACK_BYTES
    sha256: str = field(init=False)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("PinnedSpotV7CheckpointFinalityCheckerV1 cannot be subclassed")

    def __post_init__(self) -> None:
        try:
            _validate_checker_configuration(self)
            executable_sha256 = _parse_authority_manifest_v1(
                self.authority_manifest_json,
                expected_sha256=self.authority_manifest_sha256,
            )
        except (TypeError, ValueError) as exc:
            raise CheckpointFinalityCheckerAdapterRejectedV1(
                CheckpointFinalityCheckerAdapterRejectV1.AUTHORITY_MANIFEST_INVALID,
                str(exc),
            ) from exc
        object.__setattr__(self, "sha256", executable_sha256)

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False

    def cross_check_authenticated(
        self,
        *,
        policy: object,
        finality: object,
    ) -> _CrossCheckedAuthenticatedCheckpointFinalityTransitionV1:
        """Cross-check one already BLS-authenticated finality transition exactly once."""

        try:
            self._revalidate_configuration()
        except (TypeError, ValueError) as exc:
            raise CheckpointFinalityCheckerAdapterRejectedV1(
                CheckpointFinalityCheckerAdapterRejectV1.AUTHORITY_MANIFEST_INVALID,
                "checkpoint-finality checker configuration drift",
            ) from exc
        try:
            policy_value = _require_governed_operational_policy_v3(policy)
            finality_value = _require_authenticated_finality_v3(finality)
            policy_value._require_active_at_epoch_for_finality_v3(
                finality_value._projection.epoch_id
            )
            input_value = _checker_input_v1(policy_value, finality_value)
            request = _encode_checker_request_v1(input_value)
            expected = _expected_response_v1(request, input_value)
        except (TypeError, ValueError) as exc:
            raise CheckpointFinalityCheckerAdapterRejectedV1(
                CheckpointFinalityCheckerAdapterRejectV1.AUTHENTICATED_INPUT_INVALID,
                "authenticated finality failed exact checker request construction",
            ) from exc
        response = self._execute_checker(request)
        try:
            _parse_checker_response_v1(response, expected)
        except (TypeError, ValueError) as exc:
            raise CheckpointFinalityCheckerAdapterRejectedV1(
                CheckpointFinalityCheckerAdapterRejectV1.CHECKER_RESPONSE_INVALID,
                "checkpoint-finality checker response failed exact rebinding",
            ) from exc
        evidence = _CheckpointFinalityCheckerInvocationEvidenceV1(
            authority_manifest_sha256=self.authority_manifest_sha256,
            executable_sha256=self.sha256,
            request_sha256=hashlib.sha256(request).hexdigest(),
            response_sha256=hashlib.sha256(response).hexdigest(),
        )
        try:
            # Keep the only capability mint in the lexical success path that
            # performed the exact native invocation above.  A separately
            # callable "seal after execution" helper would let ordinary
            # application code skip execution and submit locally synthesized
            # response bytes to the minting boundary.
            result = object.__new__(_CrossCheckedAuthenticatedCheckpointFinalityTransitionV1)
            object.__setattr__(result, "_policy", policy_value)
            object.__setattr__(result, "_finality", finality_value)
            object.__setattr__(result, "_evidence", evidence)
            object.__setattr__(
                result,
                "_exact_authority_manifest_bytes",
                self.authority_manifest_json,
            )
            object.__setattr__(result, "_exact_request_bytes", request)
            object.__setattr__(result, "_exact_response_bytes", response)
            object.__setattr__(result, "_seal", result)
            _revalidate_cross_checked_transition_v1(result)
            return result
        except (TypeError, ValueError) as exc:
            raise CheckpointFinalityCheckerAdapterRejectedV1(
                CheckpointFinalityCheckerAdapterRejectV1.SEALED_RESULT_INVALID,
                "checkpoint-finality checker result failed private capability sealing",
            ) from exc

    def _revalidate_configuration(self) -> None:
        _validate_checker_configuration(self)
        executable_sha256 = _parse_authority_manifest_v1(
            self.authority_manifest_json,
            expected_sha256=self.authority_manifest_sha256,
        )
        if executable_sha256 != self.sha256:
            raise ValueError("checkpoint-finality checker configuration drift")

    def _execute_checker(self, request: bytes) -> bytes:
        try:
            return execute_pinned_verifier_once(
                executable=self.executable,
                expected_sha256=self.sha256,
                executable_format=VerifierExecutableFormatV1.STATIC_ELF_X86_64,
                request_bytes=request,
                timeout_seconds=self.timeout_seconds,
                max_address_space_bytes=self.max_address_space_bytes,
                max_stack_bytes=self.max_stack_bytes,
                max_stdout_bytes=RESPONSE_BYTES_V1,
                max_stderr_bytes=_MAX_CHECKER_STDERR_BYTES_V1,
            )
        except PinnedVerifierProcessError as exc:
            raise CheckpointFinalityCheckerAdapterRejectedV1(
                CheckpointFinalityCheckerAdapterRejectV1.CHECKER_REJECTED,
                "exact checkpoint-finality Rust checker rejected",
            ) from exc


def _checker_input_v1(
    policy: _GovernedSpotV7OperationalPolicyV3,
    finality: _AuthenticatedExactCheckpointFinalityTransitionV3,
) -> _CheckpointFinalityCheckerInputV1:
    store_policy = policy._base_store_policy_for_finality_v3()
    projection = finality._projection
    policy_root = _prefixed_hash_bytes(
        store_policy.checkpoint_finality_policy_root,
        "checkpoint-finality policy root",
    )
    if policy_root != _prefixed_hash_bytes(projection.policy_root, "finality policy root"):
        raise ValueError("authenticated finality policy root differs from governed policy")
    if "0x" + hashlib.sha256(finality._exact_finality_evidence_bytes).hexdigest() != (
        projection.finality_evidence_root
    ):
        raise ValueError("authenticated finality evidence root drift")
    return _CheckpointFinalityCheckerInputV1(
        policy=_CheckpointFinalityCheckerPolicyV1(
            application_id=_prefixed_hash_bytes(store_policy.application_id, "application ID"),
            chain_or_domain_id=_prefixed_hash_bytes(
                store_policy.chain_or_domain_id,
                "domain ID",
            ),
            finality_network_id=_prefixed_hash_bytes(
                store_policy.finality_network_id,
                "finality network ID",
            ),
            finality_protocol_id=_prefixed_hash_bytes(
                store_policy.finality_protocol_id,
                "finality protocol ID",
            ),
            external_finality_policy_hash=_prefixed_hash_bytes(
                store_policy.external_finality_policy_hash,
                "external finality policy hash",
            ),
            finality_verifier_set_root=_prefixed_hash_bytes(
                store_policy.finality_verifier_set_root,
                "finality verifier set root",
            ),
            genesis_application_checkpoint_sequence=(
                store_policy.genesis_application_checkpoint_sequence
            ),
            genesis_application_checkpoint_hash=_prefixed_hash_bytes(
                store_policy.genesis_application_checkpoint_hash,
                "genesis checkpoint hash",
            ),
        ),
        binding=_CheckpointFinalityCheckerBindingV1(
            application_id=_prefixed_hash_bytes(projection.application_id, "application ID"),
            chain_or_domain_id=_prefixed_hash_bytes(
                projection.chain_or_domain_id,
                "domain ID",
            ),
            epoch_id=projection.epoch_id,
            proof_journal_hash=_prefixed_hash_bytes(
                projection.proof_journal_hash,
                "proof journal hash",
            ),
            post_state_root=_prefixed_hash_bytes(projection.post_state_root, "post-state root"),
            application_checkpoint_sequence=(projection.next_application_checkpoint_sequence),
            application_checkpoint_hash=_prefixed_hash_bytes(
                projection.next_application_checkpoint_hash,
                "next checkpoint hash",
            ),
            parent_application_checkpoint_hash=_prefixed_hash_bytes(
                projection.prior_application_checkpoint_hash,
                "prior checkpoint hash",
            ),
            finality_network_id=_prefixed_hash_bytes(
                store_policy.finality_network_id,
                "finality network ID",
            ),
            finality_protocol_id=_prefixed_hash_bytes(
                store_policy.finality_protocol_id,
                "finality protocol ID",
            ),
            external_finality_policy_hash=_prefixed_hash_bytes(
                store_policy.external_finality_policy_hash,
                "external finality policy hash",
            ),
            finality_verifier_set_root=_prefixed_hash_bytes(
                store_policy.finality_verifier_set_root,
                "finality verifier set root",
            ),
            finality_evidence_root=_prefixed_hash_bytes(
                projection.finality_evidence_root,
                "finality evidence root",
            ),
            finality_policy_root=policy_root,
            certificate_root=_prefixed_hash_bytes(
                projection.certificate_root,
                "finality certificate root",
            ),
        ),
        exact_certificate_bytes=finality._exact_certificate_bytes,
    )


def _require_authenticated_finality_v3(
    value: object,
) -> _AuthenticatedExactCheckpointFinalityTransitionV3:
    if type(value) is not _AuthenticatedExactCheckpointFinalityTransitionV3:
        raise TypeError("checkpoint checker requires exact authenticated finality V3")
    typed = cast(_AuthenticatedExactCheckpointFinalityTransitionV3, value)
    if not typed._has_private_seal():
        raise TypeError("checkpoint checker requires sealed authenticated finality V3")
    return typed


def _revalidate_cross_checked_transition_v1(
    value: _CrossCheckedAuthenticatedCheckpointFinalityTransitionV1,
) -> None:
    if type(value._policy) is not _GovernedSpotV7OperationalPolicyV3:
        raise TypeError("cross-checked finality retained the wrong policy type")
    if type(value._finality) is not _AuthenticatedExactCheckpointFinalityTransitionV3:
        raise TypeError("cross-checked finality retained the wrong BLS result type")
    if type(value._evidence) is not _CheckpointFinalityCheckerInvocationEvidenceV1:
        raise TypeError("cross-checked finality retained the wrong evidence type")
    artifacts = _CheckpointFinalityCheckerInvocationArtifactsV1(
        exact_authority_manifest_bytes=value._exact_authority_manifest_bytes,
        exact_request_bytes=value._exact_request_bytes,
        exact_response_bytes=value._exact_response_bytes,
        evidence=value._evidence,
    )
    _revalidate_invocation_artifacts_v1(artifacts)
    if type(value._exact_request_bytes) is not bytes or not value._exact_request_bytes:
        raise TypeError("cross-checked finality request bytes are invalid")
    if type(value._exact_response_bytes) is not bytes:
        raise TypeError("cross-checked finality response bytes are invalid")
    input_value = _checker_input_v1(
        value._policy, _require_authenticated_finality_v3(value._finality)
    )
    request = _encode_checker_request_v1(input_value)
    if request != value._exact_request_bytes:
        raise ValueError("cross-checked finality request drift")
    if hashlib.sha256(request).hexdigest() != value._evidence.request_sha256:
        raise ValueError("cross-checked finality request digest drift")
    if hashlib.sha256(value._exact_response_bytes).hexdigest() != value._evidence.response_sha256:
        raise ValueError("cross-checked finality response digest drift")
    expected = _expected_response_v1(request, input_value)
    _parse_checker_response_v1(value._exact_response_bytes, expected)


def _revalidate_invocation_artifacts_v1(
    value: _CheckpointFinalityCheckerInvocationArtifactsV1,
) -> None:
    if (
        hashlib.sha256(value.exact_authority_manifest_bytes).hexdigest()
        != value.evidence.authority_manifest_sha256
    ):
        raise ValueError("checkpoint-finality authority manifest digest drift")
    executable_sha256 = _parse_authority_manifest_v1(
        value.exact_authority_manifest_bytes,
        expected_sha256=value.evidence.authority_manifest_sha256,
    )
    if executable_sha256 != value.evidence.executable_sha256:
        raise ValueError("checkpoint-finality executable identity drift")
    if hashlib.sha256(value.exact_request_bytes).hexdigest() != value.evidence.request_sha256:
        raise ValueError("checkpoint-finality request digest drift")
    if hashlib.sha256(value.exact_response_bytes).hexdigest() != value.evidence.response_sha256:
        raise ValueError("checkpoint-finality response digest drift")


def _validate_checker_configuration(checker: PinnedSpotV7CheckpointFinalityCheckerV1) -> None:
    if not isinstance(checker.executable, Path) or not checker.executable.is_absolute():
        raise ValueError("checker executable must be an absolute pathlib.Path")
    _require_bare_sha256(checker.authority_manifest_sha256, "authority manifest SHA-256")
    if type(checker.timeout_seconds) is not int or not 1 <= checker.timeout_seconds <= 300:
        raise ValueError("checker timeout must be in 1..300 seconds")
    if (
        type(checker.max_address_space_bytes) is not int
        or checker.max_address_space_bytes < 256 * 1_024 * 1_024
    ):
        raise ValueError("checker address-space bound is too small")
    if type(checker.max_stack_bytes) is not int or checker.max_stack_bytes < 1_024 * 1_024:
        raise ValueError("checker stack bound is too small")


def _parse_authority_manifest_v1(raw: bytes, *, expected_sha256: str) -> str:
    if type(raw) is not bytes or not raw or len(raw) > _MAX_AUTHORITY_MANIFEST_BYTES_V1:
        raise ValueError("checkpoint-finality checker authority manifest bytes are invalid")
    if hashlib.sha256(raw).hexdigest() != expected_sha256:
        raise ValueError("checkpoint-finality checker authority manifest digest mismatch")
    value = _decode_authority_manifest_v1(raw)
    if type(value) is not dict or set(value) != _MANIFEST_KEYS_V1:
        raise ValueError("checkpoint-finality checker authority manifest schema mismatch")
    if canonical_json_bytes(value) != raw:
        raise ValueError("checkpoint-finality checker authority manifest must be canonical JSON")
    expected_values = {
        "schema": CHECKPOINT_FINALITY_CHECKER_AUTHORITY_SCHEMA_V1,
        "checker_protocol_version": CHECKPOINT_FINALITY_CHECKER_PROTOCOL_VERSION_V1,
        "request_schema": CHECKPOINT_FINALITY_CHECKER_REQUEST_SCHEMA_V1,
        "response_schema": CHECKPOINT_FINALITY_CHECKER_RESPONSE_SCHEMA_V1,
        "executable_format": VerifierExecutableFormatV1.STATIC_ELF_X86_64.value,
        "release_authority": False,
        "settlement_authority": False,
        "production_authority": False,
    }
    for name, expected in expected_values.items():
        observed = value.get(name)
        if type(observed) is not type(expected) or observed != expected:
            raise ValueError(f"checkpoint-finality authority field {name} mismatch")
    executable_sha256 = value.get("executable_sha256")
    return _require_bare_sha256(executable_sha256, "checker executable SHA-256")


def _decode_authority_manifest_v1(raw: bytes) -> object:
    try:
        return json.loads(
            raw.decode("ascii"),
            object_pairs_hook=_reject_duplicate_object_keys,
            parse_float=_reject_float,
            parse_constant=_reject_json_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        raise ValueError("checkpoint-finality authority manifest must be exact JSON") from exc


def _prefixed_hash_bytes(value: object, name: str) -> bytes:
    if (
        type(value) is not str
        or len(value) != 66
        or not value.startswith("0x")
        or any(character not in "0123456789abcdef" for character in value[2:])
    ):
        raise ValueError(f"{name} must be canonical lowercase 32-byte hex")
    decoded = bytes.fromhex(value[2:])
    if decoded == bytes(32):
        raise ValueError(f"{name} must be nonzero")
    return decoded


def _require_bare_sha256(value: object, name: str) -> str:
    if type(value) is not str or len(value) != 64:
        raise ValueError(f"{name} must be lowercase 32-byte hex")
    if any(character not in "0123456789abcdef" for character in value):
        raise ValueError(f"{name} must be lowercase 32-byte hex")
    return value


def _reject_float(value: str) -> NoReturn:
    raise ValueError(f"authority manifest float is forbidden: {value}")


__all__ = [
    "CHECKPOINT_FINALITY_CHECKER_AUTHORITY_SCHEMA_V1",
    "CheckpointFinalityCheckerAdapterRejectV1",
    "CheckpointFinalityCheckerAdapterRejectedV1",
    "PinnedSpotV7CheckpointFinalityCheckerV1",
]
