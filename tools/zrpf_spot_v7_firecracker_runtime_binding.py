"""Exact authority-neutral identities for one proposed Spot V7 runtime.

The binding retains the exact canonical Firecracker configuration and runtime
manifest bytes selected by an external policy source.  It proves byte identity
only.  This module does not establish that governance or a release authority
selected those bytes, and every exposed authority property remains false.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from typing import Any, Final, NoReturn, SupportsIndex, final

from tools import zrpf_v3_firecracker_jail_staging_io as staging_io
from tools.zrpf_spot_v7_firecracker_runtime_protocol import (
    SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1,
)

_MAX_RUNTIME_MANIFEST_BYTES_V1: Final = 256 * 1024
_PREPARE_AUTHORITY_ITEMS_V1: Final = (
    ("governance_admission_verified", False),
    ("governed_machine_config_verified", False),
    ("governed_runtime_manifest_verified", False),
    ("independent_expected_digests_verified", False),
    ("production_authority", False),
    ("release_authority", False),
    ("settlement_authority", False),
)


class SpotV7FirecrackerRuntimeBindingRejectV1(ValueError):
    """Stable fail-closed rejection at the proposed-runtime identity boundary."""

    def __init__(self, code: str) -> None:
        super().__init__(code)
        self.code = code


@dataclass(frozen=True, slots=True, init=False)
class ProposedSpotV7FirecrackerRuntimeBindingV1:
    """Exact proposal bytes without governance, release, or execution authority."""

    exact_machine_config_bytes: bytes
    exact_runtime_manifest_bytes: bytes
    machine_config_sha256: bytes
    runtime_manifest_sha256: bytes

    def __new__(cls) -> ProposedSpotV7FirecrackerRuntimeBindingV1:
        raise TypeError("runtime binding requires validated construction")

    @classmethod
    def validated(
        cls,
        *,
        exact_machine_config_bytes: bytes,
        exact_runtime_manifest_bytes: bytes,
        runtime_profile_sha256: bytes,
    ) -> ProposedSpotV7FirecrackerRuntimeBindingV1:
        if (
            type(runtime_profile_sha256) is not bytes
            or runtime_profile_sha256
            != SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1
        ):
            raise SpotV7FirecrackerRuntimeBindingRejectV1(
                "runtime_binding_profile"
            )
        try:
            staging_io.validate_config_bytes(exact_machine_config_bytes)
        except (TypeError, ValueError) as exc:
            raise SpotV7FirecrackerRuntimeBindingRejectV1(
                "runtime_binding_machine_config"
            ) from exc
        _validate_manifest_bytes(exact_runtime_manifest_bytes)
        value = object.__new__(cls)
        object.__setattr__(
            value,
            "exact_machine_config_bytes",
            exact_machine_config_bytes,
        )
        object.__setattr__(
            value,
            "exact_runtime_manifest_bytes",
            exact_runtime_manifest_bytes,
        )
        object.__setattr__(
            value,
            "machine_config_sha256",
            hashlib.sha256(exact_machine_config_bytes).digest(),
        )
        object.__setattr__(
            value,
            "runtime_manifest_sha256",
            hashlib.sha256(exact_runtime_manifest_bytes).digest(),
        )
        return value

    @property
    def runtime_profile_sha256(self) -> bytes:
        return SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1

    @property
    def governance_admission_verified(self) -> bool:
        return False

    @property
    def governed_machine_config_verified(self) -> bool:
        return False

    @property
    def governed_runtime_manifest_verified(self) -> bool:
        return False

    @property
    def independent_expected_digests_verified(self) -> bool:
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


class _PrepareObservationSealV1:
    __slots__ = ()


_PREPARE_OBSERVATION_SEAL_V1 = _PrepareObservationSealV1()


@final
class SpotV7FirecrackerPrepareObservationV1:
    """Ordinary retained evidence derived from one prepared runtime binding."""

    __slots__ = ("_binding", "_request_sha256", "_seal")

    _binding: ProposedSpotV7FirecrackerRuntimeBindingV1
    _request_sha256: bytes
    _seal: _PrepareObservationSealV1

    def __init__(
        self,
        *,
        binding: ProposedSpotV7FirecrackerRuntimeBindingV1,
        request_sha256: bytes,
        seal: _PrepareObservationSealV1,
    ) -> None:
        if seal is not _PREPARE_OBSERVATION_SEAL_V1:
            raise TypeError("prepare observation requires the module-private seal")
        if type(binding) is not ProposedSpotV7FirecrackerRuntimeBindingV1:
            raise TypeError("prepare observation requires an exact runtime binding")
        _require_digest(request_sha256, "prepare_observation_request")
        object.__setattr__(self, "_binding", binding)
        object.__setattr__(self, "_request_sha256", request_sha256)
        object.__setattr__(self, "_seal", seal)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("SpotV7FirecrackerPrepareObservationV1 cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("prepare observation cannot be mutated")

    def __reduce__(self) -> NoReturn:
        raise TypeError("prepare observation cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("prepare observation cannot be serialized")

    @property
    def runtime_binding(self) -> ProposedSpotV7FirecrackerRuntimeBindingV1:
        return self._binding

    @property
    def request_sha256(self) -> bytes:
        return self._request_sha256

    def runtime_binding_document(self) -> dict[str, str]:
        return {
            "exact_machine_config_ascii": (
                self._binding.exact_machine_config_bytes.decode("ascii")
            ),
            "exact_runtime_manifest_ascii": (
                self._binding.exact_runtime_manifest_bytes.decode("ascii")
            ),
            "machine_config_sha256": self._binding.machine_config_sha256.hex(),
            "request_sha256": self._request_sha256.hex(),
            "runtime_manifest_sha256": (
                self._binding.runtime_manifest_sha256.hex()
            ),
            "runtime_profile_sha256": self._binding.runtime_profile_sha256.hex(),
        }

    def to_document(self) -> dict[str, Any]:
        return {
            "authority": dict(_PREPARE_AUTHORITY_ITEMS_V1),
            "runtime_binding": self.runtime_binding_document(),
            "schema": "zenodex/zrpf_spot_v7_firecracker_prepare_observation/v1",
            "scope": "exact_proposed_runtime_identity_authority_false",
        }

    def canonical_bytes(self) -> bytes:
        return canonical_document_bytes(self.to_document())


def _new_prepare_observation(
    binding: ProposedSpotV7FirecrackerRuntimeBindingV1,
    *,
    request_sha256: bytes,
) -> SpotV7FirecrackerPrepareObservationV1:
    return SpotV7FirecrackerPrepareObservationV1(
        binding=binding,
        request_sha256=request_sha256,
        seal=_PREPARE_OBSERVATION_SEAL_V1,
    )


def canonical_document_bytes(value: object) -> bytes:
    return (
        json.dumps(value, ensure_ascii=True, separators=(",", ":"), sort_keys=True)
        + "\n"
    ).encode("ascii")


def _validate_manifest_bytes(raw: bytes) -> None:
    if type(raw) is not bytes or not 0 < len(raw) <= _MAX_RUNTIME_MANIFEST_BYTES_V1:
        raise SpotV7FirecrackerRuntimeBindingRejectV1(
            "runtime_binding_manifest"
        )
    try:
        document = json.loads(
            raw.decode("ascii"),
            object_pairs_hook=_unique_object,
            parse_constant=_reject_constant,
            parse_float=_reject_float,
        )
    except (
        UnicodeDecodeError,
        json.JSONDecodeError,
        RecursionError,
        ValueError,
    ) as exc:
        raise SpotV7FirecrackerRuntimeBindingRejectV1(
            "runtime_binding_manifest"
        ) from exc
    if type(document) is not dict or raw != canonical_document_bytes(document):
        raise SpotV7FirecrackerRuntimeBindingRejectV1(
            "runtime_binding_manifest"
        )


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    output: dict[str, Any] = {}
    for key, value in pairs:
        if key in output:
            raise ValueError("duplicate key")
        output[key] = value
    return output


def _reject_constant(_value: str) -> None:
    raise ValueError("non-finite number")


def _reject_float(_value: str) -> None:
    raise ValueError("floating-point number")


def _require_digest(value: bytes, code: str) -> None:
    if type(value) is not bytes or len(value) != 32 or not any(value):
        raise SpotV7FirecrackerRuntimeBindingRejectV1(code)
