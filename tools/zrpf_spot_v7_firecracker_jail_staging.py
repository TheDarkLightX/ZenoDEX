"""Exact authority-neutral Spot V7 binding over shared jail staging."""

from __future__ import annotations

import hashlib
from pathlib import Path
from typing import NoReturn, SupportsIndex, final

from tools.zrpf_spot_v7_firecracker_runtime_binding import (
    ProposedSpotV7FirecrackerRuntimeBindingV1,
    SpotV7FirecrackerPrepareObservationV1,
    _new_prepare_observation,
)
from tools.zrpf_spot_v7_firecracker_runtime_protocol import (
    SPOT_V7_FIRECRACKER_REQUEST_BYTES_V1,
    SpotV7FirecrackerProtocolRejectV1,
    decode_exact_request_v1,
)
from tools.zrpf_v3_firecracker_jail_staging import (
    PreparedJailRootSpecV2,
    PreparedJailRootV2,
    RootOwnedStagedArtifactV2,
    _prepare_validated_root_owned_jail,
    _StagedOutputProtocolV1,
    _validate_shared_prepare_inputs,
)
from tools.zrpf_v3_firecracker_trusted_runtime import JailerLauncherReject

__all__ = [
    "PreparedSpotV7JailRootV1",
    "prepare_root_owned_spot_v7_jail_v1",
]


class _PreparedSpotV7JailRootSealV1:
    __slots__ = ()


_PREPARED_SPOT_V7_JAIL_ROOT_SEAL_V1 = _PreparedSpotV7JailRootSealV1()


@final
class PreparedSpotV7JailRootV1:
    """One exact proposed V7 runtime staged without application authority."""

    __slots__ = ("_inner", "_request_sha256", "_runtime_binding", "_seal")

    _inner: PreparedJailRootV2
    _request_sha256: bytes
    _runtime_binding: ProposedSpotV7FirecrackerRuntimeBindingV1
    _seal: _PreparedSpotV7JailRootSealV1

    def __init__(
        self,
        *,
        inner: PreparedJailRootV2,
        request_sha256: bytes,
        runtime_binding: ProposedSpotV7FirecrackerRuntimeBindingV1,
        seal: _PreparedSpotV7JailRootSealV1,
    ) -> None:
        if seal is not _PREPARED_SPOT_V7_JAIL_ROOT_SEAL_V1:
            raise TypeError("prepared Spot V7 jail requires the module-private seal")
        if (
            type(inner) is not PreparedJailRootV2
            or inner._output_protocol is not _StagedOutputProtocolV1.SPOT_V7_V1
            or type(request_sha256) is not bytes
            or len(request_sha256) != 32
            or not any(request_sha256)
            or type(runtime_binding) is not ProposedSpotV7FirecrackerRuntimeBindingV1
        ):
            raise TypeError("prepared Spot V7 jail inputs have invalid types")
        object.__setattr__(self, "_inner", inner)
        object.__setattr__(self, "_request_sha256", request_sha256)
        object.__setattr__(self, "_runtime_binding", runtime_binding)
        object.__setattr__(self, "_seal", seal)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("PreparedSpotV7JailRootV1 cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("prepared Spot V7 jail cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("prepared Spot V7 jail cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("prepared Spot V7 jail cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("prepared Spot V7 jail cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("prepared Spot V7 jail cannot be serialized")

    @property
    def spec(self) -> PreparedJailRootSpecV2:
        return self._inner.spec

    @property
    def jail_root_path(self) -> Path:
        return self._inner.jail_root_path

    @property
    def runtime_binding(self) -> ProposedSpotV7FirecrackerRuntimeBindingV1:
        return self._runtime_binding

    def verify_prelaunch(self) -> None:
        self._inner.verify_prelaunch()

    def prepare_observation(self) -> SpotV7FirecrackerPrepareObservationV1:
        self.verify_prelaunch()
        return _new_prepare_observation(
            self._runtime_binding,
            request_sha256=self._request_sha256,
        )

    def read_validated_output_after_exit(self) -> bytes:
        return self._inner.read_validated_output_after_exit()

    def _exact_request_bytes_for_supervisor_v1(self) -> bytes:
        """Expose the retained canonical request only to the local supervisor."""

        self.verify_prelaunch()
        return self._inner._request_bytes

    def cleanup_after_teardown(self) -> None:
        self._inner.cleanup_after_teardown()

    def abandon_before_launch(self) -> None:
        self._inner.abandon_before_launch()


def prepare_root_owned_spot_v7_jail_v1(
    *,
    spec: PreparedJailRootSpecV2,
    artifacts: tuple[RootOwnedStagedArtifactV2, ...],
    config_bytes: bytes,
    request_bytes: bytes,
    runtime_binding: ProposedSpotV7FirecrackerRuntimeBindingV1,
    trusted_chroot_root: Path = Path("/"),
    trusted_source_root: Path = Path("/"),
) -> PreparedSpotV7JailRootV1:
    """Stage one V7 request bound to exact proposed config and manifest bytes."""

    _validate_spot_v7_prepare_inputs(
        spec=spec,
        artifacts=artifacts,
        config_bytes=config_bytes,
        request_bytes=request_bytes,
        runtime_binding=runtime_binding,
    )
    inner = _prepare_validated_root_owned_jail(
        spec=spec,
        artifacts=artifacts,
        config_bytes=config_bytes,
        request_bytes=request_bytes,
        output_protocol=_StagedOutputProtocolV1.SPOT_V7_V1,
        trusted_chroot_root=trusted_chroot_root,
        trusted_source_root=trusted_source_root,
    )
    return PreparedSpotV7JailRootV1(
        inner=inner,
        request_sha256=hashlib.sha256(request_bytes).digest(),
        runtime_binding=runtime_binding,
        seal=_PREPARED_SPOT_V7_JAIL_ROOT_SEAL_V1,
    )


def _validate_spot_v7_prepare_inputs(
    *,
    spec: PreparedJailRootSpecV2,
    artifacts: tuple[RootOwnedStagedArtifactV2, ...],
    config_bytes: bytes,
    request_bytes: bytes,
    runtime_binding: ProposedSpotV7FirecrackerRuntimeBindingV1,
) -> None:
    if type(runtime_binding) is not ProposedSpotV7FirecrackerRuntimeBindingV1:
        raise TypeError(
            "runtime_binding must be exact ProposedSpotV7FirecrackerRuntimeBindingV1"
        )
    _validate_shared_prepare_inputs(spec, artifacts, config_bytes)
    if config_bytes != runtime_binding.exact_machine_config_bytes:
        raise JailerLauncherReject("jail_stage_spot_v7_machine_config_binding")
    if (
        type(request_bytes) is not bytes
        or len(request_bytes) != SPOT_V7_FIRECRACKER_REQUEST_BYTES_V1
    ):
        raise JailerLauncherReject("jail_stage_request_invalid")
    try:
        decoded_request = decode_exact_request_v1(request_bytes)
    except SpotV7FirecrackerProtocolRejectV1 as exc:
        raise JailerLauncherReject("jail_stage_request_invalid") from exc
    if decoded_request.encode() != request_bytes:
        raise JailerLauncherReject("jail_stage_request_noncanonical")
    if decoded_request.runtime_manifest_sha256 != runtime_binding.runtime_manifest_sha256:
        raise JailerLauncherReject("jail_stage_spot_v7_runtime_manifest_binding")
    if decoded_request.machine_config_sha256 != runtime_binding.machine_config_sha256:
        raise JailerLauncherReject("jail_stage_spot_v7_machine_config_binding")
    input_artifact = next(
        artifact for artifact in artifacts if artifact.role == "input"
    )
    if decoded_request.input_drive_sha256.hex() != input_artifact.sha256:
        raise JailerLauncherReject("jail_stage_spot_v7_input_binding")
