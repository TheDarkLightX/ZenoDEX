"""Governed exact-content adapter for the Spot V7 full-blob DA prerequisite.

The adapter executes one pinned static Rust verifier exactly once. The verifier
checks the canonical ``full_blob_da_v1`` certificate, exact blob bytes, and the
release-bound local policy material. Only the exact fixed-width success record
can mint the private V2 DA capability consumed by the operational join.

This module establishes local exact-content and policy satisfaction. It does not
establish provider replication, network retrievability, future retention,
external finality, settlement authority, release authority, or production
authority.
"""

from __future__ import annotations

import hashlib
import hmac
import re
from dataclasses import dataclass
from pathlib import Path
from typing import NoReturn, Self, final

from src.integration._zeno_ledger_pinned_verifier_process_v1 import (
    DEFAULT_VERIFIER_ADDRESS_SPACE_BYTES,
    DEFAULT_VERIFIER_STACK_BYTES,
    PinnedVerifierProcessError,
    VerifierExecutableFormatV1,
    execute_pinned_verifier_once,
)
from src.integration._zrpf_spot_v7_operational_capability_v2 import (
    _GOVERNED_EXACT_FULL_BLOB_POLICY_SEAL_V2,
    _GovernedExactFullBlobPolicySatisfactionV2,
)
from src.integration._zrpf_spot_v7_operational_gate import (
    _GovernedFullBlobPolicyProjectionV1,
)
from src.integration._zrpf_spot_v7_operational_mechanics import (
    MAX_FULL_BLOB_BYTES_V1,
    MAX_FULL_BLOB_CERTIFICATE_BYTES_V1,
)
from src.integration.zrpf_spot_v7_operational_policy_adapter import (
    TrustedSpotV7OperationalPolicyBindingV1,
)

REQUEST_MAGIC_V1 = b"ZDAREQ1\x00"
RESPONSE_MAGIC_V1 = b"ZDAOK1\x00\x00"
REQUEST_VERSION_V1 = 1
RESPONSE_BYTES_V1 = 160
MAX_U64 = (1 << 64) - 1
MAX_U32 = (1 << 32) - 1
DEFAULT_DA_VERIFIER_TIMEOUT_SECONDS_V1 = 30
_HASH_RE = re.compile(r"^0x[0-9a-f]{64}$")
_BARE_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


class FullBlobDaAdapterError(ValueError):
    """Stable fail-closed error from the governed local DA adapter."""

    def __init__(self, code: str, detail: str) -> None:
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}")


@final
@dataclass(frozen=True, slots=True)
class PinnedFullBlobDaPolicyVerifierV1:
    """One release-selected static verifier executable and execution envelope."""

    executable: Path
    expected_sha256: str
    expected_authority_manifest_sha256: str
    timeout_seconds: int = DEFAULT_DA_VERIFIER_TIMEOUT_SECONDS_V1
    max_address_space_bytes: int = DEFAULT_VERIFIER_ADDRESS_SPACE_BYTES
    max_stack_bytes: int = DEFAULT_VERIFIER_STACK_BYTES

    def __post_init__(self) -> None:
        if type(self.executable) is not Path or not self.executable.is_absolute():
            raise FullBlobDaAdapterError(
                "VERIFIER_PATH_INVALID",
                "full-blob verifier path must be an absolute pathlib.Path",
            )
        _require_bare_sha256(
            self.expected_sha256,
            name="expected_sha256",
            code="VERIFIER_SHA256_INVALID",
        )
        _require_bare_sha256(
            self.expected_authority_manifest_sha256,
            name="expected_authority_manifest_sha256",
            code="AUTHORITY_MANIFEST_SHA256_INVALID",
        )
        _require_positive_bounded_int(
            self.timeout_seconds,
            name="timeout_seconds",
            maximum=300,
            code="TIMEOUT_INVALID",
        )
        _require_positive_bounded_int(
            self.max_address_space_bytes,
            name="max_address_space_bytes",
            maximum=16 * 1024 * 1024 * 1024,
            code="ADDRESS_SPACE_LIMIT_INVALID",
        )
        _require_positive_bounded_int(
            self.max_stack_bytes,
            name="max_stack_bytes",
            maximum=1024 * 1024 * 1024,
            code="STACK_LIMIT_INVALID",
        )

    def verify_and_seal(
        self,
        *,
        policy: TrustedSpotV7OperationalPolicyBindingV1,
        exact_certificate_bytes: bytes,
        exact_blob_bytes: bytes,
        expected_certificate_epoch: int,
        checked_epoch: int,
    ) -> TrustedFullBlobDaPolicySatisfactionV1:
        """Execute the exact checker once and mint one sealed DA prerequisite."""

        if type(policy) is not TrustedSpotV7OperationalPolicyBindingV1:
            raise FullBlobDaAdapterError(
                "POLICY_TYPE_INVALID",
                "policy must be the exact release-bound operational-policy type",
            )
        if not hmac.compare_digest(
            policy.authority_manifest_sha256,
            self.expected_authority_manifest_sha256,
        ):
            raise FullBlobDaAdapterError(
                "AUTHORITY_MANIFEST_MISMATCH",
                "DA verifier and operational policy use different authority manifests",
            )
        certificate = _require_exact_bytes(
            exact_certificate_bytes,
            name="exact_certificate_bytes",
            maximum=MAX_FULL_BLOB_CERTIFICATE_BYTES_V1,
            code="CERTIFICATE_BYTES_INVALID",
        )
        blob = _require_exact_bytes(
            exact_blob_bytes,
            name="exact_blob_bytes",
            maximum=MAX_FULL_BLOB_BYTES_V1,
            code="BLOB_BYTES_INVALID",
        )
        certificate_epoch = _require_u64(
            expected_certificate_epoch,
            name="expected_certificate_epoch",
            code="CERTIFICATE_EPOCH_INVALID",
        )
        checked = _require_u64(
            checked_epoch,
            name="checked_epoch",
            code="CHECKED_EPOCH_INVALID",
        )

        policy_capability = policy._capability_for_operational_gate()
        store_policy = policy_capability._policy_for_atomic_store()
        request = _request_bytes_v1(
            application_id=store_policy.application_id,
            chain_or_domain_id=store_policy.chain_or_domain_id,
            data_schema_id=store_policy.data_schema_id,
            storage_policy_hash=store_policy.storage_policy_hash,
            minimum_retention_epochs=store_policy.minimum_retention_epochs,
            minimum_remaining_epochs=store_policy.minimum_remaining_epochs,
            maximum_blob_bytes=store_policy.maximum_blob_bytes,
            expected_certificate_epoch=certificate_epoch,
            checked_epoch=checked,
            exact_certificate_bytes=certificate,
            exact_blob_bytes=blob,
        )
        request_sha256 = hashlib.sha256(request).hexdigest()
        try:
            response = execute_pinned_verifier_once(
                executable=self.executable,
                expected_sha256=self.expected_sha256,
                executable_format=VerifierExecutableFormatV1.STATIC_ELF_X86_64,
                request_bytes=request,
                timeout_seconds=self.timeout_seconds,
                max_address_space_bytes=self.max_address_space_bytes,
                max_stack_bytes=self.max_stack_bytes,
                max_stdout_bytes=RESPONSE_BYTES_V1,
                max_stderr_bytes=16 * 1024,
            )
        except PinnedVerifierProcessError as exc:
            raise FullBlobDaAdapterError(
                "PINNED_VERIFIER_REJECTED",
                f"{exc.reason.value}: {exc.detail}",
            ) from exc

        parsed = _parse_success_response_v1(response)
        if parsed.policy_root != store_policy.full_blob_policy_root:
            raise FullBlobDaAdapterError(
                "POLICY_ROOT_MISMATCH",
                "Rust verifier output does not bind the governed policy root",
            )
        if parsed.epoch_id != certificate_epoch:
            raise FullBlobDaAdapterError(
                "CERTIFICATE_EPOCH_MISMATCH",
                "Rust verifier output changed the expected certificate epoch",
            )
        if parsed.checked_epoch != checked:
            raise FullBlobDaAdapterError(
                "CHECKED_EPOCH_MISMATCH",
                "Rust verifier output changed the governed checked epoch",
            )
        expected_blob_sha256 = "0x" + hashlib.sha256(blob).hexdigest()
        if not hmac.compare_digest(parsed.exact_blob_sha256, expected_blob_sha256):
            raise FullBlobDaAdapterError(
                "EXACT_BLOB_SHA256_MISMATCH",
                "Rust verifier output does not bind the supplied exact blob",
            )

        projection = _GovernedFullBlobPolicyProjectionV1(
            application_id=store_policy.application_id,
            chain_or_domain_id=store_policy.chain_or_domain_id,
            epoch_id=parsed.epoch_id,
            certificate_root=parsed.certificate_root,
            data_root=parsed.data_root,
            policy_root=parsed.policy_root,
            exact_blob_sha256=parsed.exact_blob_sha256,
            checked_epoch=parsed.checked_epoch,
            retention_through_epoch=parsed.retention_through_epoch,
        )
        capability = _GovernedExactFullBlobPolicySatisfactionV2(
            projection,
            exact_blob_bytes=blob,
            exact_certificate_bytes=certificate,
            seal=_GOVERNED_EXACT_FULL_BLOB_POLICY_SEAL_V2,
        )
        return TrustedFullBlobDaPolicySatisfactionV1._from_verified(
            capability=capability,
            policy_manifest_digest=policy.manifest_digest,
            verifier_sha256=self.expected_sha256,
            verification_request_sha256=request_sha256,
            projection=parsed,
        )


@dataclass(frozen=True, slots=True)
class _ParsedFullBlobDaSuccessV1:
    policy_root: str
    certificate_root: str
    data_root: str
    exact_blob_sha256: str
    epoch_id: int
    checked_epoch: int
    retention_through_epoch: int


@final
@dataclass(frozen=True, init=False, slots=True)
class TrustedFullBlobDaPolicySatisfactionV1:
    """Nonconstructible verified result carrying the sealed V2 DA capability."""

    policy_manifest_digest: str
    verifier_sha256: str
    verification_request_sha256: str
    policy_root: str
    certificate_root: str
    data_root: str
    exact_blob_sha256: str
    epoch_id: int
    checked_epoch: int
    retention_through_epoch: int
    _capability: _GovernedExactFullBlobPolicySatisfactionV2

    def __new__(cls) -> Self:
        raise TypeError("trusted full-blob DA results must be created by the pinned adapter")

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("trusted full-blob DA results cannot be subclassed")

    def __reduce__(self) -> NoReturn:
        raise TypeError("trusted full-blob DA results cannot be serialized")

    def __reduce_ex__(self, _protocol: object) -> NoReturn:
        raise TypeError("trusted full-blob DA results cannot be serialized")

    @classmethod
    def _from_verified(
        cls,
        *,
        capability: _GovernedExactFullBlobPolicySatisfactionV2,
        policy_manifest_digest: str,
        verifier_sha256: str,
        verification_request_sha256: str,
        projection: _ParsedFullBlobDaSuccessV1,
    ) -> TrustedFullBlobDaPolicySatisfactionV1:
        if type(capability) is not _GovernedExactFullBlobPolicySatisfactionV2:
            raise TypeError("verified DA capability has the wrong type")
        if not capability._has_private_seal():
            raise TypeError("verified DA capability lacks its private seal")
        value = object.__new__(cls)
        object.__setattr__(value, "policy_manifest_digest", policy_manifest_digest)
        object.__setattr__(value, "verifier_sha256", verifier_sha256)
        object.__setattr__(
            value,
            "verification_request_sha256",
            verification_request_sha256,
        )
        object.__setattr__(value, "policy_root", projection.policy_root)
        object.__setattr__(value, "certificate_root", projection.certificate_root)
        object.__setattr__(value, "data_root", projection.data_root)
        object.__setattr__(value, "exact_blob_sha256", projection.exact_blob_sha256)
        object.__setattr__(value, "epoch_id", projection.epoch_id)
        object.__setattr__(value, "checked_epoch", projection.checked_epoch)
        object.__setattr__(
            value,
            "retention_through_epoch",
            projection.retention_through_epoch,
        )
        object.__setattr__(value, "_capability", capability)
        return value

    def _capability_for_operational_gate(self) -> _GovernedExactFullBlobPolicySatisfactionV2:
        capability = self._capability
        if type(capability) is not _GovernedExactFullBlobPolicySatisfactionV2:
            raise TypeError("trusted DA result lost its exact capability type")
        if not capability._has_private_seal():
            raise TypeError("trusted DA result lost its private governed seal")
        return capability

    @property
    def retrievability_verified(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


def _request_bytes_v1(
    *,
    application_id: str,
    chain_or_domain_id: str,
    data_schema_id: str,
    storage_policy_hash: str,
    minimum_retention_epochs: int,
    minimum_remaining_epochs: int,
    maximum_blob_bytes: int,
    expected_certificate_epoch: int,
    checked_epoch: int,
    exact_certificate_bytes: bytes,
    exact_blob_bytes: bytes,
) -> bytes:
    certificate_length = len(exact_certificate_bytes)
    blob_length = len(exact_blob_bytes)
    if certificate_length > MAX_U32 or blob_length > MAX_U32:
        raise FullBlobDaAdapterError(
            "REQUEST_LENGTH_OVERFLOW",
            "DA verifier request component exceeds u32 framing",
        )
    return b"".join(
        (
            REQUEST_MAGIC_V1,
            REQUEST_VERSION_V1.to_bytes(2, "big"),
            _hash_bytes(application_id, name="application_id"),
            _hash_bytes(chain_or_domain_id, name="chain_or_domain_id"),
            _hash_bytes(data_schema_id, name="data_schema_id"),
            _hash_bytes(storage_policy_hash, name="storage_policy_hash"),
            _require_u64(minimum_retention_epochs, name="minimum_retention_epochs", code="POLICY_FIELD_INVALID").to_bytes(8, "big"),
            _require_u64(minimum_remaining_epochs, name="minimum_remaining_epochs", code="POLICY_FIELD_INVALID").to_bytes(8, "big"),
            _require_u64(maximum_blob_bytes, name="maximum_blob_bytes", code="POLICY_FIELD_INVALID").to_bytes(8, "big"),
            expected_certificate_epoch.to_bytes(8, "big"),
            checked_epoch.to_bytes(8, "big"),
            certificate_length.to_bytes(4, "big"),
            blob_length.to_bytes(4, "big"),
            exact_certificate_bytes,
            exact_blob_bytes,
        )
    )


def _parse_success_response_v1(raw: bytes) -> _ParsedFullBlobDaSuccessV1:
    if type(raw) is not bytes or len(raw) != RESPONSE_BYTES_V1:
        raise FullBlobDaAdapterError(
            "VERIFIER_RESPONSE_LENGTH",
            f"full-blob verifier response must be exactly {RESPONSE_BYTES_V1} bytes",
        )
    if raw[:8] != RESPONSE_MAGIC_V1:
        raise FullBlobDaAdapterError(
            "VERIFIER_RESPONSE_MAGIC",
            "full-blob verifier response magic mismatch",
        )
    return _ParsedFullBlobDaSuccessV1(
        policy_root=_prefixed_hash(raw[8:40]),
        certificate_root=_prefixed_hash(raw[40:72]),
        data_root=_prefixed_hash(raw[72:104]),
        exact_blob_sha256=_prefixed_hash(raw[104:136]),
        epoch_id=int.from_bytes(raw[136:144], "big"),
        checked_epoch=int.from_bytes(raw[144:152], "big"),
        retention_through_epoch=int.from_bytes(raw[152:160], "big"),
    )


def _prefixed_hash(raw: bytes) -> str:
    if len(raw) != 32 or not any(raw):
        raise FullBlobDaAdapterError(
            "VERIFIER_RESPONSE_HASH",
            "full-blob verifier returned a zero or malformed hash",
        )
    return "0x" + raw.hex()


def _hash_bytes(value: object, *, name: str) -> bytes:
    if type(value) is not str or _HASH_RE.fullmatch(value) is None:
        raise FullBlobDaAdapterError(
            "POLICY_HASH_INVALID",
            f"{name} must be canonical lowercase 0x-prefixed 32-byte hex",
        )
    raw = bytes.fromhex(value[2:])
    if not any(raw):
        raise FullBlobDaAdapterError("POLICY_HASH_INVALID", f"{name} must be nonzero")
    return raw


def _require_bare_sha256(value: object, *, name: str, code: str) -> str:
    if type(value) is not str or _BARE_SHA256_RE.fullmatch(value) is None:
        raise FullBlobDaAdapterError(code, f"{name} must be lowercase 64-character hex")
    return value


def _require_u64(value: object, *, name: str, code: str) -> int:
    if type(value) is not int or value < 0 or value > MAX_U64:
        raise FullBlobDaAdapterError(code, f"{name} must be an unsigned 64-bit integer")
    return value


def _require_positive_bounded_int(
    value: object,
    *,
    name: str,
    maximum: int,
    code: str,
) -> int:
    if type(value) is not int or value <= 0 or value > maximum:
        raise FullBlobDaAdapterError(code, f"{name} must be in 1..={maximum}")
    return value


def _require_exact_bytes(value: object, *, name: str, maximum: int, code: str) -> bytes:
    if type(value) is not bytes or not value or len(value) > maximum:
        raise FullBlobDaAdapterError(code, f"{name} must be nonempty bytes within {maximum}")
    return value


__all__ = [
    "DEFAULT_DA_VERIFIER_TIMEOUT_SECONDS_V1",
    "FullBlobDaAdapterError",
    "PinnedFullBlobDaPolicyVerifierV1",
    "TrustedFullBlobDaPolicySatisfactionV1",
]
