"""Pinned exact ``full_blob_da_v1`` checker adapter for Spot V7.

The adapter accepts one already-sealed governed operational policy, snapshots
and executes the exact manifest-pinned Rust checker under the shared pre-exec
process contract, rebinds the fixed response to the complete request, and only
then constructs the private exact-byte DA capability. The result establishes a
local content-and-policy check for this invocation. It carries no provider,
settlement, release, or production authority.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import NoReturn, final

from src.integration._zeno_ledger_pinned_verifier_process_v1 import (
    PinnedVerifierProcessError,
    VerifierExecutableFormatV1,
    execute_pinned_verifier_once,
)
from src.integration._zrpf_spot_v7_full_blob_da_codec import (
    FULL_BLOB_DA_CHECKER_PROTOCOL_VERSION_V1,
    FULL_BLOB_DA_CHECKER_REQUEST_SCHEMA_V1,
    FULL_BLOB_DA_CHECKER_RESPONSE_SCHEMA_V1,
    RESPONSE_BYTES_V1,
    _encode_checker_request_v1,
    _expected_response_v1,
    _ExpectedFullBlobDaResponseV1,
    _FullBlobDaCheckInputV1,
    _ParsedFullBlobDaResponseV1,
)
from src.integration._zrpf_spot_v7_full_blob_da_codec import (
    _parse_checker_response_v1 as _parse_checker_response_raw_v1,
)
from src.integration._zrpf_spot_v7_operational_capability_v2 import (
    _GOVERNED_EXACT_FULL_BLOB_POLICY_SEAL_V2,
    _GovernedExactFullBlobPolicySatisfactionV2,
    _GovernedSpotV7OperationalPolicyV2,
)
from src.integration._zrpf_spot_v7_operational_gate import (
    _GovernedFullBlobPolicyProjectionV1,
)
from src.integration.recursive_stark_verifier_adapter import (
    DEFAULT_VERIFIER_ADDRESS_SPACE_BYTES,
    DEFAULT_VERIFIER_STACK_BYTES,
    _reject_duplicate_object_keys,
    _reject_json_constant,
)
from src.state.canonical import canonical_json_bytes

FULL_BLOB_DA_CHECKER_AUTHORITY_SCHEMA_V1 = "zenodex.zrpf.full_blob_da_checker_authority.v1"

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
        "settlement_authority",
        "production_authority",
    }
)


class FullBlobDaAdapterRejectV1(str, Enum):
    AUTHORITY_MANIFEST_INVALID = "authority_manifest_invalid"
    REQUEST_INVALID = "request_invalid"
    CHECKER_REJECTED = "checker_rejected"
    CHECKER_RESPONSE_INVALID = "checker_response_invalid"
    CAPABILITY_BINDING_INVALID = "capability_binding_invalid"


class FullBlobDaAdapterRejectedV1(ValueError):
    """Stable fail-closed rejection from the exact Rust checker boundary."""

    def __init__(self, reason: FullBlobDaAdapterRejectV1, detail: str) -> None:
        self.reason = reason
        self.detail = detail
        super().__init__(f"{reason.value}: {detail}")


@final
@dataclass(frozen=True)
class PinnedFullBlobDataAvailabilityCheckerV1:
    """One manifest-pinned exact checker; release governance stays external."""

    executable: Path
    authority_manifest_json: bytes
    authority_manifest_sha256: str
    timeout_seconds: int = 30
    max_address_space_bytes: int = DEFAULT_VERIFIER_ADDRESS_SPACE_BYTES
    max_stack_bytes: int = DEFAULT_VERIFIER_STACK_BYTES
    sha256: str = field(init=False)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("PinnedFullBlobDataAvailabilityCheckerV1 cannot be subclassed")

    def __post_init__(self) -> None:
        try:
            _validate_checker_configuration(self)
            executable_sha256 = _parse_authority_manifest_v1(
                self.authority_manifest_json,
                expected_sha256=self.authority_manifest_sha256,
            )
        except (TypeError, ValueError) as exc:
            raise FullBlobDaAdapterRejectedV1(
                FullBlobDaAdapterRejectV1.AUTHORITY_MANIFEST_INVALID,
                str(exc),
            ) from exc
        object.__setattr__(self, "sha256", executable_sha256)

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False

    def check_exact(
        self,
        *,
        policy: object,
        expected_certificate_epoch: int,
        checked_epoch: int,
        exact_certificate_bytes: bytes,
        exact_blob_bytes: bytes,
    ) -> _GovernedExactFullBlobPolicySatisfactionV2:
        """Run the exact checker and retain the identical policy and artifacts."""

        if type(policy) is not _GovernedSpotV7OperationalPolicyV2:
            raise TypeError("DA checker requires the exact governed Spot V7 operational policy")
        try:
            input_value = _FullBlobDaCheckInputV1(
                policy,
                expected_certificate_epoch,
                checked_epoch,
                exact_certificate_bytes,
                exact_blob_bytes,
            )
            request = _encode_checker_request_v1(input_value)
            expected = _expected_response_v1(request, input_value)
        except (TypeError, ValueError) as exc:
            raise FullBlobDaAdapterRejectedV1(
                FullBlobDaAdapterRejectV1.REQUEST_INVALID,
                "full-blob checker request failed bounded canonical encoding",
            ) from exc
        response = self._execute_checker(request)
        parsed = _parse_checker_response_v1(response, expected=expected)
        return _bind_exact_capability_v1(input_value, expected, parsed)

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
            raise FullBlobDaAdapterRejectedV1(
                FullBlobDaAdapterRejectV1.CHECKER_REJECTED,
                "exact full-blob Rust checker rejected",
            ) from exc


def _validate_checker_configuration(
    checker: PinnedFullBlobDataAvailabilityCheckerV1,
) -> None:
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


def _bind_exact_capability_v1(
    input_value: _FullBlobDaCheckInputV1,
    expected: _ExpectedFullBlobDaResponseV1,
    parsed: _ParsedFullBlobDaResponseV1,
) -> _GovernedExactFullBlobPolicySatisfactionV2:
    try:
        projection = _GovernedFullBlobPolicyProjectionV1(
            application_id="0x" + expected.application_id.hex(),
            chain_or_domain_id="0x" + expected.chain_or_domain_id.hex(),
            epoch_id=expected.expected_certificate_epoch,
            certificate_root="0x" + parsed.certificate_root.hex(),
            data_root="0x" + parsed.data_root.hex(),
            policy_root="0x" + expected.policy_root.hex(),
            exact_blob_sha256="0x" + expected.exact_blob_sha256.hex(),
            checked_epoch=expected.checked_epoch,
            retention_through_epoch=parsed.retention_through_epoch,
        )
        return _GovernedExactFullBlobPolicySatisfactionV2(
            projection,
            governed_policy=input_value.policy,
            exact_blob_bytes=input_value.exact_blob_bytes,
            exact_certificate_bytes=input_value.exact_certificate_bytes,
            seal=_GOVERNED_EXACT_FULL_BLOB_POLICY_SEAL_V2,
        )
    except (TypeError, ValueError) as exc:
        raise FullBlobDaAdapterRejectedV1(
            FullBlobDaAdapterRejectV1.CAPABILITY_BINDING_INVALID,
            "exact Rust result failed governed capability rebinding",
        ) from exc


def _parse_checker_response_v1(
    raw: bytes,
    *,
    expected: _ExpectedFullBlobDaResponseV1,
) -> _ParsedFullBlobDaResponseV1:
    try:
        return _parse_checker_response_raw_v1(raw, expected)
    except (TypeError, ValueError) as exc:
        raise FullBlobDaAdapterRejectedV1(
            FullBlobDaAdapterRejectV1.CHECKER_RESPONSE_INVALID,
            "full-blob checker response failed exact rebinding",
        ) from exc


def _parse_authority_manifest_v1(raw: bytes, *, expected_sha256: str) -> str:
    if type(raw) is not bytes or not raw or len(raw) > _MAX_AUTHORITY_MANIFEST_BYTES_V1:
        raise ValueError("full-blob checker authority manifest bytes are invalid")
    if hashlib.sha256(raw).hexdigest() != expected_sha256:
        raise ValueError("full-blob checker authority manifest digest mismatch")
    value = _decode_authority_manifest_v1(raw)
    if type(value) is not dict or set(value) != _MANIFEST_KEYS_V1:
        raise ValueError("full-blob checker authority manifest schema mismatch")
    if canonical_json_bytes(value) != raw:
        raise ValueError("full-blob checker authority manifest must be canonical JSON")
    _require_authority_manifest_values_v1(value)
    executable_sha256 = value.get("executable_sha256")
    if type(executable_sha256) is not str:
        raise ValueError("checker executable SHA-256 must be a string")
    _require_bare_sha256(executable_sha256, "checker executable SHA-256")
    return executable_sha256


def _decode_authority_manifest_v1(raw: bytes) -> object:
    try:
        return json.loads(
            raw.decode("ascii"),
            object_pairs_hook=_reject_duplicate_object_keys,
            parse_float=_reject_float,
            parse_constant=_reject_json_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        raise ValueError("full-blob checker authority manifest must be exact JSON") from exc


def _require_authority_manifest_values_v1(value: dict[object, object]) -> None:
    expected_values = {
        "schema": FULL_BLOB_DA_CHECKER_AUTHORITY_SCHEMA_V1,
        "checker_protocol_version": FULL_BLOB_DA_CHECKER_PROTOCOL_VERSION_V1,
        "request_schema": FULL_BLOB_DA_CHECKER_REQUEST_SCHEMA_V1,
        "response_schema": FULL_BLOB_DA_CHECKER_RESPONSE_SCHEMA_V1,
        "executable_format": VerifierExecutableFormatV1.STATIC_ELF_X86_64.value,
        "settlement_authority": False,
        "production_authority": False,
    }
    for name, expected in expected_values.items():
        observed = value.get(name)
        if type(observed) is not type(expected) or observed != expected:
            raise ValueError(f"full-blob checker authority field {name} mismatch")


def _require_bare_sha256(value: object, name: str) -> None:
    if type(value) is not str or len(value) != 64:
        raise ValueError(f"{name} must be lowercase 32-byte hex")
    if any(character not in "0123456789abcdef" for character in value):
        raise ValueError(f"{name} must be lowercase 32-byte hex")


def _reject_float(value: str) -> NoReturn:
    raise ValueError(f"authority manifest float is forbidden: {value}")


__all__ = [
    "FullBlobDaAdapterRejectV1",
    "FullBlobDaAdapterRejectedV1",
    "PinnedFullBlobDataAvailabilityCheckerV1",
]
