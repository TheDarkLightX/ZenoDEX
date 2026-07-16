"""Fixed wire codec for the proof-neutral checkpoint-finality V2 checker.

The checker response commitment is framing integrity only.  Authentication is
provided by executing the manifest-pinned checker over an already sealed BLS
finality transition and comparing every returned field with this independently
constructed request.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass

CHECKPOINT_FINALITY_CHECKER_PROTOCOL_VERSION_V1 = 1
CHECKPOINT_FINALITY_CHECKER_REQUEST_SCHEMA_V1 = (
    "zenodex.zrpf.checkpoint_finality_checker.request.v1"
)
CHECKPOINT_FINALITY_CHECKER_RESPONSE_SCHEMA_V1 = (
    "zenodex.zrpf.checkpoint_finality_checker.response.v1"
)

REQUEST_MAGIC_V1 = b"ZRPFCFV2REQV1!!!"
RESPONSE_MAGIC_V1 = b"ZRPFCFV2RESV1!!!"
PRIOR_CURSOR_EMPTY_V1 = 0
PRIOR_CURSOR_RECORD_V1 = 1
PRIOR_CURSOR_RECORD_BYTES_V1 = 264
REQUEST_HEADER_BYTES_V1 = 885
MAX_CERTIFICATE_BYTES_V1 = 576
RESPONSE_BODY_BYTES_V1 = 298
RESPONSE_BYTES_V1 = 330
MAX_U64 = (1 << 64) - 1
RESPONSE_COMMITMENT_DOMAIN_V1 = b"zenodex.zrpf.checkpoint_finality_checker.response_commitment.v1"


@dataclass(frozen=True, slots=True)
class _CheckpointFinalityCheckerPolicyV1:
    application_id: bytes
    chain_or_domain_id: bytes
    finality_network_id: bytes
    finality_protocol_id: bytes
    external_finality_policy_hash: bytes
    finality_verifier_set_root: bytes
    genesis_application_checkpoint_sequence: int
    genesis_application_checkpoint_hash: bytes

    def __post_init__(self) -> None:
        for name in (
            "application_id",
            "chain_or_domain_id",
            "finality_network_id",
            "finality_protocol_id",
            "external_finality_policy_hash",
            "finality_verifier_set_root",
            "genesis_application_checkpoint_hash",
        ):
            _require_hash(getattr(self, name), name=name)
        _require_u64(
            self.genesis_application_checkpoint_sequence,
            name="genesis application checkpoint sequence",
        )


@dataclass(frozen=True, slots=True)
class _CheckpointFinalityCheckerBindingV1:
    application_id: bytes
    chain_or_domain_id: bytes
    epoch_id: int
    proof_journal_hash: bytes
    post_state_root: bytes
    application_checkpoint_sequence: int
    application_checkpoint_hash: bytes
    parent_application_checkpoint_hash: bytes
    finality_network_id: bytes
    finality_protocol_id: bytes
    external_finality_policy_hash: bytes
    finality_verifier_set_root: bytes
    finality_evidence_root: bytes
    finality_policy_root: bytes
    certificate_root: bytes

    def __post_init__(self) -> None:
        for name in (
            "application_id",
            "chain_or_domain_id",
            "proof_journal_hash",
            "post_state_root",
            "application_checkpoint_hash",
            "parent_application_checkpoint_hash",
            "finality_network_id",
            "finality_protocol_id",
            "external_finality_policy_hash",
            "finality_verifier_set_root",
            "finality_evidence_root",
            "finality_policy_root",
            "certificate_root",
        ):
            _require_hash(getattr(self, name), name=name)
        _require_u64(self.epoch_id, name="epoch ID")
        _require_u64(
            self.application_checkpoint_sequence,
            name="application checkpoint sequence",
        )
        if self.application_checkpoint_sequence == 0:
            raise ValueError("application checkpoint sequence has no prior cursor")


@dataclass(frozen=True, slots=True)
class _CheckpointFinalityCheckerInputV1:
    policy: _CheckpointFinalityCheckerPolicyV1
    binding: _CheckpointFinalityCheckerBindingV1
    exact_certificate_bytes: bytes

    def __post_init__(self) -> None:
        if type(self.policy) is not _CheckpointFinalityCheckerPolicyV1:
            raise TypeError("checkpoint-finality checker policy has the wrong type")
        if type(self.binding) is not _CheckpointFinalityCheckerBindingV1:
            raise TypeError("checkpoint-finality checker binding has the wrong type")
        if (
            type(self.exact_certificate_bytes) is not bytes
            or not self.exact_certificate_bytes
            or len(self.exact_certificate_bytes) > MAX_CERTIFICATE_BYTES_V1
        ):
            raise ValueError("checkpoint-finality certificate bytes are empty or oversized")
        _require_scope_consistency(self.policy, self.binding)


@dataclass(frozen=True, slots=True)
class _ExpectedCheckpointFinalityResponseV1:
    application_id: bytes
    chain_or_domain_id: bytes
    epoch_id: int
    policy_root: bytes
    certificate_root: bytes
    prior_application_checkpoint_sequence: int
    prior_application_checkpoint_hash: bytes
    next_application_checkpoint_sequence: int
    next_application_checkpoint_hash: bytes
    exact_certificate_sha256: bytes
    request_sha256: bytes

    def __post_init__(self) -> None:
        for name in (
            "application_id",
            "chain_or_domain_id",
            "policy_root",
            "certificate_root",
            "prior_application_checkpoint_hash",
            "next_application_checkpoint_hash",
            "exact_certificate_sha256",
            "request_sha256",
        ):
            _require_hash(getattr(self, name), name=f"expected response {name}")
        for name in (
            "epoch_id",
            "prior_application_checkpoint_sequence",
            "next_application_checkpoint_sequence",
        ):
            _require_u64(getattr(self, name), name=f"expected response {name}")
        if self.prior_application_checkpoint_sequence == MAX_U64:
            raise ValueError("expected response prior cursor overflows")
        if self.next_application_checkpoint_sequence != (
            self.prior_application_checkpoint_sequence + 1
        ):
            raise ValueError("expected response cursor is not an exact successor")


@dataclass(frozen=True, slots=True)
class _ParsedCheckpointFinalityResponseV1:
    policy_root: bytes
    certificate_root: bytes
    prior_application_checkpoint_sequence: int
    prior_application_checkpoint_hash: bytes
    next_application_checkpoint_sequence: int
    next_application_checkpoint_hash: bytes


def _encode_checker_request_v1(value: _CheckpointFinalityCheckerInputV1) -> bytes:
    if type(value) is not _CheckpointFinalityCheckerInputV1:
        raise TypeError("checkpoint-finality checker input has the wrong type")
    policy = value.policy
    binding = value.binding
    prior_sequence = binding.application_checkpoint_sequence - 1
    certificate_length = len(value.exact_certificate_bytes)
    request = b"".join(
        (
            REQUEST_MAGIC_V1,
            CHECKPOINT_FINALITY_CHECKER_PROTOCOL_VERSION_V1.to_bytes(2, "big"),
            policy.application_id,
            policy.chain_or_domain_id,
            policy.finality_network_id,
            policy.finality_protocol_id,
            policy.external_finality_policy_hash,
            policy.finality_verifier_set_root,
            policy.genesis_application_checkpoint_sequence.to_bytes(8, "big"),
            policy.genesis_application_checkpoint_hash,
            binding.application_id,
            binding.chain_or_domain_id,
            binding.epoch_id.to_bytes(8, "big"),
            binding.proof_journal_hash,
            binding.post_state_root,
            binding.application_checkpoint_sequence.to_bytes(8, "big"),
            binding.application_checkpoint_hash,
            binding.parent_application_checkpoint_hash,
            binding.finality_network_id,
            binding.finality_protocol_id,
            binding.external_finality_policy_hash,
            binding.finality_verifier_set_root,
            binding.finality_evidence_root,
            _encode_prior_cursor_v1(policy, binding, prior_sequence),
            certificate_length.to_bytes(2, "big"),
            value.exact_certificate_bytes,
        )
    )
    if len(request) != REQUEST_HEADER_BYTES_V1 + certificate_length:
        raise ValueError("checkpoint-finality checker request framing mismatch")
    return request


def _encode_prior_cursor_v1(
    policy: _CheckpointFinalityCheckerPolicyV1,
    binding: _CheckpointFinalityCheckerBindingV1,
    prior_sequence: int,
) -> bytes:
    if prior_sequence == policy.genesis_application_checkpoint_sequence:
        return bytes((PRIOR_CURSOR_EMPTY_V1,)) + bytes(PRIOR_CURSOR_RECORD_BYTES_V1)
    record = b"".join(
        (
            policy.application_id,
            policy.chain_or_domain_id,
            policy.finality_network_id,
            policy.finality_protocol_id,
            policy.external_finality_policy_hash,
            policy.finality_verifier_set_root,
            binding.finality_policy_root,
            prior_sequence.to_bytes(8, "big"),
            binding.parent_application_checkpoint_hash,
        )
    )
    if len(record) != PRIOR_CURSOR_RECORD_BYTES_V1:
        raise ValueError("checkpoint-finality prior cursor framing mismatch")
    return bytes((PRIOR_CURSOR_RECORD_V1,)) + record


def _expected_response_v1(
    request: bytes,
    value: _CheckpointFinalityCheckerInputV1,
) -> _ExpectedCheckpointFinalityResponseV1:
    if type(request) is not bytes:
        raise TypeError("checkpoint-finality checker request must be exact bytes")
    if type(value) is not _CheckpointFinalityCheckerInputV1:
        raise TypeError("checkpoint-finality checker input has the wrong type")
    binding = value.binding
    return _ExpectedCheckpointFinalityResponseV1(
        application_id=binding.application_id,
        chain_or_domain_id=binding.chain_or_domain_id,
        epoch_id=binding.epoch_id,
        policy_root=binding.finality_policy_root,
        certificate_root=binding.certificate_root,
        prior_application_checkpoint_sequence=(binding.application_checkpoint_sequence - 1),
        prior_application_checkpoint_hash=binding.parent_application_checkpoint_hash,
        next_application_checkpoint_sequence=binding.application_checkpoint_sequence,
        next_application_checkpoint_hash=binding.application_checkpoint_hash,
        exact_certificate_sha256=hashlib.sha256(value.exact_certificate_bytes).digest(),
        request_sha256=hashlib.sha256(request).digest(),
    )


def _parse_checker_response_v1(
    raw: bytes,
    expected: _ExpectedCheckpointFinalityResponseV1,
) -> _ParsedCheckpointFinalityResponseV1:
    if type(expected) is not _ExpectedCheckpointFinalityResponseV1:
        raise TypeError("expected checkpoint-finality response has the wrong type")
    body = _validated_response_body(raw)
    reader = _ResponseReaderV1(body)
    if reader.read(16) != RESPONSE_MAGIC_V1:
        raise ValueError("checkpoint-finality response magic mismatch")
    if reader.u16() != CHECKPOINT_FINALITY_CHECKER_PROTOCOL_VERSION_V1:
        raise ValueError("checkpoint-finality response version mismatch")
    observed = _ExpectedCheckpointFinalityResponseV1(
        application_id=reader.read(32),
        chain_or_domain_id=reader.read(32),
        epoch_id=reader.u64(),
        policy_root=reader.read(32),
        certificate_root=reader.read(32),
        prior_application_checkpoint_sequence=reader.u64(),
        prior_application_checkpoint_hash=reader.read(32),
        next_application_checkpoint_sequence=reader.u64(),
        next_application_checkpoint_hash=reader.read(32),
        exact_certificate_sha256=reader.read(32),
        request_sha256=reader.read(32),
    )
    reader.finished()
    if observed != expected:
        raise ValueError("checkpoint-finality response does not bind the exact request")
    return _ParsedCheckpointFinalityResponseV1(
        policy_root=observed.policy_root,
        certificate_root=observed.certificate_root,
        prior_application_checkpoint_sequence=(observed.prior_application_checkpoint_sequence),
        prior_application_checkpoint_hash=observed.prior_application_checkpoint_hash,
        next_application_checkpoint_sequence=(observed.next_application_checkpoint_sequence),
        next_application_checkpoint_hash=observed.next_application_checkpoint_hash,
    )


def _validated_response_body(raw: bytes) -> bytes:
    if type(raw) is not bytes or len(raw) != RESPONSE_BYTES_V1:
        raise ValueError("checkpoint-finality response byte length mismatch")
    body = raw[:RESPONSE_BODY_BYTES_V1]
    observed = raw[RESPONSE_BODY_BYTES_V1:]
    required = hashlib.sha256(RESPONSE_COMMITMENT_DOMAIN_V1 + body).digest()
    if observed != required:
        raise ValueError("checkpoint-finality response commitment mismatch")
    return body


def _require_scope_consistency(
    policy: _CheckpointFinalityCheckerPolicyV1,
    binding: _CheckpointFinalityCheckerBindingV1,
) -> None:
    pairs = (
        (binding.application_id, policy.application_id),
        (binding.chain_or_domain_id, policy.chain_or_domain_id),
        (binding.finality_network_id, policy.finality_network_id),
        (binding.finality_protocol_id, policy.finality_protocol_id),
        (binding.external_finality_policy_hash, policy.external_finality_policy_hash),
        (binding.finality_verifier_set_root, policy.finality_verifier_set_root),
    )
    if any(observed != required for observed, required in pairs):
        raise ValueError("checkpoint-finality request scope differs from governed policy")
    prior_sequence = binding.application_checkpoint_sequence - 1
    if prior_sequence < policy.genesis_application_checkpoint_sequence:
        raise ValueError("checkpoint-finality prior cursor precedes governed genesis")
    if (
        prior_sequence == policy.genesis_application_checkpoint_sequence
        and binding.parent_application_checkpoint_hash != policy.genesis_application_checkpoint_hash
    ):
        raise ValueError("checkpoint-finality prior cursor replaces governed genesis")


def _require_hash(value: object, *, name: str) -> None:
    if type(value) is not bytes or len(value) != 32 or value == bytes(32):
        raise ValueError(f"{name} must be exact nonzero 32-byte bytes")


def _require_u64(value: object, *, name: str) -> None:
    if type(value) is not int or not 0 <= value <= MAX_U64:
        raise ValueError(f"{name} must be an unsigned 64-bit integer")


class _ResponseReaderV1:
    __slots__ = ("_offset", "_raw")

    def __init__(self, raw: bytes) -> None:
        self._raw = raw
        self._offset = 0

    def read(self, length: int) -> bytes:
        end = self._offset + length
        value = self._raw[self._offset : end]
        if len(value) != length:
            raise ValueError("checkpoint-finality response is truncated")
        self._offset = end
        return value

    def u16(self) -> int:
        return int.from_bytes(self.read(2), "big")

    def u64(self) -> int:
        return int.from_bytes(self.read(8), "big")

    def finished(self) -> None:
        if self._offset != len(self._raw):
            raise ValueError("checkpoint-finality response contains trailing bytes")


__all__: list[str] = []
