"""Descriptor-bound artifact identities for the Spot V7 Firecracker lane.

The factory opens the complete closed artifact inventory, hashes each bounded
regular file through its retained descriptor, and only then constructs the
runtime binding. The result retains those descriptors so a later path lookup
cannot silently substitute bytes. This establishes local artifact-byte and
descriptor identity only. Governance, release, execution, privacy, settlement,
and production authority remain false.
"""

from __future__ import annotations

import os
import stat
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, Final, NoReturn, SupportsIndex, final

from tools import zrpf_v3_firecracker_jail_staging_io as staging_io
from tools.zrpf_spot_v7_firecracker_runtime_manifest import (
    SPOT_V7_RUNTIME_ARTIFACT_NAMES_V1,
    SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1,
    CandidateSpotV7FirecrackerRuntimeManifestV1,
    SpotV7RuntimeArtifactIdentityV1,
    SpotV7RuntimeManifestRejectV1,
    parse_exact_candidate_spot_v7_runtime_manifest_v1,
)
from tools.zrpf_spot_v7_firecracker_runtime_protocol import (
    SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1,
)
from tools.zrpf_v3_firecracker_trusted_runtime import JailerLauncherReject

if TYPE_CHECKING:
    from types import TracebackType

    from tools.zrpf_spot_v7_firecracker_runtime_binding import (
        ProposedSpotV7FirecrackerRuntimeBindingV1,
    )

_MAX_TRUSTED_UID_V1: Final = (1 << 31) - 1
_MAX_SOURCE_PATH_BYTES_V1: Final = 4_096


class SpotV7RuntimeArtifactBindingRejectV1(ValueError):
    """Stable fail-closed rejection at the descriptor-binding boundary."""

    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(code)


@dataclass(frozen=True, slots=True, init=False)
class SpotV7RuntimeArtifactSourceV1:
    """One untrusted role-to-path proposal for the closed runtime inventory."""

    role: str
    source_path: Path

    def __new__(cls) -> SpotV7RuntimeArtifactSourceV1:
        raise TypeError("artifact source requires validated construction")

    @classmethod
    def validated(
        cls,
        *,
        role: str,
        source_path: Path,
    ) -> SpotV7RuntimeArtifactSourceV1:
        if type(role) is not str or role not in SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1:
            raise SpotV7RuntimeArtifactBindingRejectV1("runtime_artifact_role")
        _require_bounded_absolute_path(
            source_path,
            code="runtime_artifact_path",
        )
        value = object.__new__(cls)
        object.__setattr__(value, "role", role)
        object.__setattr__(value, "source_path", source_path)
        return value


@dataclass(frozen=True, slots=True)
class _OpenedRuntimeArtifactV1:
    role: str
    source_path: Path
    descriptor: int
    version: staging_io.FileVersionV2
    expected_sha256: str
    expected_size: int


class _OpenedArtifactSetSealV1:
    __slots__ = ()


_OPENED_ARTIFACT_SET_SEAL_V1 = _OpenedArtifactSetSealV1()


@final
class _OpenedSpotV7RuntimeArtifactSetV1:
    """Private process-local capability retaining every verified descriptor."""

    __slots__ = ("_closed", "_records", "_seal")

    _closed: bool
    _records: tuple[_OpenedRuntimeArtifactV1, ...]
    _seal: _OpenedArtifactSetSealV1

    def __init__(
        self,
        *,
        records: tuple[_OpenedRuntimeArtifactV1, ...],
        seal: _OpenedArtifactSetSealV1,
    ) -> None:
        if seal is not _OPENED_ARTIFACT_SET_SEAL_V1:
            raise TypeError("opened artifact set requires the module-private seal")
        if tuple(record.role for record in records) != SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1:
            raise TypeError("opened artifact set requires the exact role inventory")
        object.__setattr__(self, "_records", records)
        object.__setattr__(self, "_seal", seal)
        object.__setattr__(self, "_closed", False)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("opened artifact set cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("opened artifact set cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("opened artifact set cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("opened artifact set cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("opened artifact set cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("opened artifact set cannot be serialized")

    def __del__(self) -> None:
        if hasattr(self, "_closed"):
            self.close()

    @property
    def roles(self) -> tuple[str, ...]:
        self.require_open()
        return tuple(record.role for record in self._records)

    def reverify(self) -> None:
        """Rehash the retained files and require their original path identities."""

        self.require_open()
        for record in self._records:
            _reverify_opened_artifact(record)

    def require_manifest(
        self,
        manifest: CandidateSpotV7FirecrackerRuntimeManifestV1,
    ) -> None:
        self.require_open()
        if type(manifest) is not CandidateSpotV7FirecrackerRuntimeManifestV1:
            raise TypeError("opened artifact set requires an exact manifest")
        expected = tuple(
            (
                artifact.role,
                artifact.artifact_name,
                artifact.sha256.hex(),
                artifact.size_bytes,
            )
            for artifact in manifest.artifacts
        )
        actual = tuple(
            (
                record.role,
                record.source_path.name,
                record.expected_sha256,
                record.expected_size,
            )
            for record in self._records
        )
        if actual != expected:
            raise TypeError("opened artifact set does not match the exact manifest")

    def close(self) -> None:
        if self._closed:
            return
        for record in self._records:
            try:
                os.close(record.descriptor)
            except OSError:
                pass
        object.__setattr__(self, "_closed", True)

    def require_open(self) -> None:
        if self._closed or self._seal is not _OPENED_ARTIFACT_SET_SEAL_V1:
            raise SpotV7RuntimeArtifactBindingRejectV1(
                "runtime_artifact_binding_closed"
            )


class _DescriptorBoundRuntimeSealV1:
    __slots__ = ()


_DESCRIPTOR_BOUND_RUNTIME_SEAL_V1 = _DescriptorBoundRuntimeSealV1()


@final
class _DescriptorBoundSpotV7FirecrackerRuntimeBindingV1:
    """Private exact runtime binding backed by six retained descriptors."""

    __slots__ = ("_artifacts", "_proposal", "_seal", "_spent")

    _artifacts: _OpenedSpotV7RuntimeArtifactSetV1
    _proposal: ProposedSpotV7FirecrackerRuntimeBindingV1
    _seal: _DescriptorBoundRuntimeSealV1
    _spent: bool

    def __init__(
        self,
        *,
        proposal: ProposedSpotV7FirecrackerRuntimeBindingV1,
        artifacts: _OpenedSpotV7RuntimeArtifactSetV1,
        seal: _DescriptorBoundRuntimeSealV1,
    ) -> None:
        if seal is not _DESCRIPTOR_BOUND_RUNTIME_SEAL_V1:
            raise TypeError("descriptor-bound runtime requires the module-private seal")
        from tools.zrpf_spot_v7_firecracker_runtime_binding import (
            ProposedSpotV7FirecrackerRuntimeBindingV1,
        )

        if type(proposal) is not ProposedSpotV7FirecrackerRuntimeBindingV1:
            raise TypeError("descriptor-bound runtime requires an exact proposal")
        if type(artifacts) is not _OpenedSpotV7RuntimeArtifactSetV1:
            raise TypeError("descriptor-bound runtime requires an exact artifact set")
        artifacts.require_open()
        artifacts.require_manifest(proposal.runtime_manifest)
        object.__setattr__(self, "_proposal", proposal)
        object.__setattr__(self, "_artifacts", artifacts)
        object.__setattr__(self, "_seal", seal)
        object.__setattr__(self, "_spent", False)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("descriptor-bound runtime cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("descriptor-bound runtime cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("descriptor-bound runtime cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("descriptor-bound runtime cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("descriptor-bound runtime cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("descriptor-bound runtime cannot be serialized")

    def __del__(self) -> None:
        artifacts = getattr(self, "_artifacts", None)
        if artifacts is not None:
            artifacts.close()

    def __enter__(self) -> _DescriptorBoundSpotV7FirecrackerRuntimeBindingV1:
        self.reverify_artifacts()
        return self

    def __exit__(
        self,
        _exc_type: type[BaseException] | None,
        _exc_value: BaseException | None,
        _traceback: TracebackType | None,
    ) -> None:
        self.close()

    @property
    def artifact_roles(self) -> tuple[str, ...]:
        return self._artifacts.roles

    @property
    def exact_machine_config_bytes(self) -> bytes:
        self._require_open()
        return self._proposal.exact_machine_config_bytes

    @property
    def exact_runtime_manifest_bytes(self) -> bytes:
        self._require_open()
        return self._proposal.exact_runtime_manifest_bytes

    @property
    def machine_config_sha256(self) -> bytes:
        self._require_open()
        return self._proposal.machine_config_sha256

    @property
    def runtime_manifest_sha256(self) -> bytes:
        self._require_open()
        return self._proposal.runtime_manifest_sha256

    @property
    def runtime_manifest(self) -> CandidateSpotV7FirecrackerRuntimeManifestV1:
        self._require_open()
        return self._proposal.runtime_manifest

    @property
    def runtime_profile_sha256(self) -> bytes:
        self._require_open()
        return self._proposal.runtime_profile_sha256

    @property
    def artifact_bytes_verified(self) -> bool:
        self._require_open()
        return True

    @property
    def descriptor_identity_verified(self) -> bool:
        self._require_open()
        return True

    @property
    def governance_admission_verified(self) -> bool:
        self._require_open()
        return False

    @property
    def governed_runtime_manifest_verified(self) -> bool:
        self._require_open()
        return False

    @property
    def live_firecracker_execution_verified(self) -> bool:
        self._require_open()
        return False

    @property
    def release_authority(self) -> bool:
        self._require_open()
        return False

    @property
    def settlement_authority(self) -> bool:
        self._require_open()
        return False

    @property
    def production_authority(self) -> bool:
        self._require_open()
        return False

    @property
    def witness_privacy(self) -> bool:
        self._require_open()
        return False

    @property
    def zero_knowledge_privacy(self) -> bool:
        self._require_open()
        return False

    def reverify_artifacts(self) -> None:
        self._artifacts.reverify()

    def _take_for_descriptor_staging_v1(
        self,
    ) -> tuple[
        ProposedSpotV7FirecrackerRuntimeBindingV1,
        tuple[_OpenedRuntimeArtifactV1, ...],
    ]:
        """Spend this binding and lend its retained descriptors to staging.

        The descriptor bridge is process-local Python code, so the leading
        underscore is an information-hiding boundary rather than protection
        from hostile code in the same interpreter.  Marking the capability
        spent before the final rehash makes every staging attempt one-shot,
        including failed attempts.
        """

        if self._spent:
            raise SpotV7RuntimeArtifactBindingRejectV1(
                "runtime_artifact_binding_spent"
            )
        self._require_open()
        object.__setattr__(self, "_spent", True)
        try:
            self._artifacts.reverify()
            return self._proposal, self._artifacts._records
        except BaseException:
            self.close()
            raise

    def close(self) -> None:
        self._artifacts.close()

    def _require_open(self) -> None:
        if self._seal is not _DESCRIPTOR_BOUND_RUNTIME_SEAL_V1:
            raise SpotV7RuntimeArtifactBindingRejectV1(
                "runtime_artifact_binding_closed"
            )
        self._artifacts.require_open()


def open_descriptor_bound_spot_v7_runtime_binding_v1(
    *,
    exact_machine_config_bytes: bytes,
    exact_runtime_manifest_bytes: bytes,
    artifact_sources: tuple[SpotV7RuntimeArtifactSourceV1, ...],
    runtime_profile_sha256: bytes,
    trusted_source_root: Path,
    trusted_uid: int,
) -> _DescriptorBoundSpotV7FirecrackerRuntimeBindingV1:
    """Open the exact artifact set before constructing its runtime binding."""

    if (
        type(runtime_profile_sha256) is not bytes
        or runtime_profile_sha256 != SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1
    ):
        raise SpotV7RuntimeArtifactBindingRejectV1("runtime_artifact_runtime_profile")
    manifest = _parse_manifest(
        exact_runtime_manifest_bytes,
        exact_machine_config_bytes=exact_machine_config_bytes,
    )
    opened = _open_exact_artifact_set(
        manifest=manifest,
        artifact_sources=artifact_sources,
        trusted_source_root=trusted_source_root,
        trusted_uid=trusted_uid,
    )
    try:
        from tools.zrpf_spot_v7_firecracker_runtime_binding import (
            ProposedSpotV7FirecrackerRuntimeBindingV1,
            SpotV7FirecrackerRuntimeBindingRejectV1,
        )

        try:
            proposal = ProposedSpotV7FirecrackerRuntimeBindingV1.validated(
                exact_machine_config_bytes=exact_machine_config_bytes,
                exact_runtime_manifest_bytes=exact_runtime_manifest_bytes,
                runtime_profile_sha256=runtime_profile_sha256,
            )
        except SpotV7FirecrackerRuntimeBindingRejectV1 as exc:
            raise SpotV7RuntimeArtifactBindingRejectV1(
                "runtime_artifact_runtime_binding"
            ) from exc
        if proposal.runtime_manifest.artifact_set_id != manifest.artifact_set_id:
            raise SpotV7RuntimeArtifactBindingRejectV1(
                "runtime_artifact_runtime_binding"
            )
        return _DescriptorBoundSpotV7FirecrackerRuntimeBindingV1(
            proposal=proposal,
            artifacts=opened,
            seal=_DESCRIPTOR_BOUND_RUNTIME_SEAL_V1,
        )
    except BaseException:
        opened.close()
        raise


def _parse_manifest(
    raw: bytes,
    *,
    exact_machine_config_bytes: bytes,
) -> CandidateSpotV7FirecrackerRuntimeManifestV1:
    try:
        return parse_exact_candidate_spot_v7_runtime_manifest_v1(
            raw,
            exact_machine_config_bytes=exact_machine_config_bytes,
        )
    except SpotV7RuntimeManifestRejectV1 as exc:
        raise SpotV7RuntimeArtifactBindingRejectV1("runtime_artifact_manifest") from exc


def _open_exact_artifact_set(
    *,
    manifest: CandidateSpotV7FirecrackerRuntimeManifestV1,
    artifact_sources: tuple[SpotV7RuntimeArtifactSourceV1, ...],
    trusted_source_root: Path,
    trusted_uid: int,
) -> _OpenedSpotV7RuntimeArtifactSetV1:
    sources = _require_exact_source_inventory(artifact_sources)
    _require_trusted_root_and_uid(trusted_source_root, trusted_uid)
    opened: list[_OpenedRuntimeArtifactV1] = []
    result: _OpenedSpotV7RuntimeArtifactSetV1 | None = None
    try:
        for expected, source in zip(manifest.artifacts, sources, strict=True):
            opened.append(
                _open_one_artifact(
                    expected=expected,
                    source=source,
                    trusted_source_root=trusted_source_root,
                    trusted_uid=trusted_uid,
                )
            )
        result = _OpenedSpotV7RuntimeArtifactSetV1(
            records=tuple(opened),
            seal=_OPENED_ARTIFACT_SET_SEAL_V1,
        )
        result.reverify()
        return result
    except BaseException:
        if result is not None:
            result.close()
        else:
            for record in opened:
                try:
                    os.close(record.descriptor)
                except OSError:
                    pass
        raise


def _require_exact_source_inventory(
    value: tuple[SpotV7RuntimeArtifactSourceV1, ...],
) -> tuple[SpotV7RuntimeArtifactSourceV1, ...]:
    if (
        type(value) is not tuple
        or len(value) != len(SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1)
        or any(type(source) is not SpotV7RuntimeArtifactSourceV1 for source in value)
    ):
        raise SpotV7RuntimeArtifactBindingRejectV1("runtime_artifact_inventory")
    for source in value:
        _require_source_shape(source)
    roles = tuple(source.role for source in value)
    if len(set(roles)) != len(roles):
        raise SpotV7RuntimeArtifactBindingRejectV1("runtime_artifact_duplicate_role")
    paths = tuple(str(source.source_path) for source in value)
    if len(set(paths)) != len(paths):
        raise SpotV7RuntimeArtifactBindingRejectV1("runtime_artifact_duplicate_path")
    if roles != SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1:
        raise SpotV7RuntimeArtifactBindingRejectV1("runtime_artifact_inventory")
    for source in value:
        if source.source_path.name != SPOT_V7_RUNTIME_ARTIFACT_NAMES_V1[source.role]:
            raise SpotV7RuntimeArtifactBindingRejectV1("runtime_artifact_path")
    return value


def _require_source_shape(source: SpotV7RuntimeArtifactSourceV1) -> None:
    if (
        type(source.role) is not str
        or source.role not in SPOT_V7_RUNTIME_ARTIFACT_ROLES_V1
    ):
        raise SpotV7RuntimeArtifactBindingRejectV1("runtime_artifact_role")
    _require_bounded_absolute_path(
        source.source_path,
        code="runtime_artifact_path",
    )


def _require_trusted_root_and_uid(trusted_root: Path, trusted_uid: int) -> None:
    _require_bounded_absolute_path(
        trusted_root,
        code="runtime_artifact_trusted_root",
    )
    if type(trusted_uid) is not int or not 0 <= trusted_uid <= _MAX_TRUSTED_UID_V1:
        raise SpotV7RuntimeArtifactBindingRejectV1("runtime_artifact_trusted_uid")


def _require_bounded_absolute_path(path: Path, *, code: str) -> None:
    if (
        not isinstance(path, Path)
        or not path.is_absolute()
        or any(part in {"", ".", ".."} for part in path.parts)
    ):
        raise SpotV7RuntimeArtifactBindingRejectV1(code)
    try:
        raw = os.fsencode(path)
    except (TypeError, ValueError, UnicodeError) as exc:
        raise SpotV7RuntimeArtifactBindingRejectV1(code) from exc
    if not raw or b"\x00" in raw or len(raw) > _MAX_SOURCE_PATH_BYTES_V1:
        raise SpotV7RuntimeArtifactBindingRejectV1(code)


def _open_one_artifact(
    *,
    expected: SpotV7RuntimeArtifactIdentityV1,
    source: SpotV7RuntimeArtifactSourceV1,
    trusted_source_root: Path,
    trusted_uid: int,
) -> _OpenedRuntimeArtifactV1:
    if source.role != expected.role:
        raise SpotV7RuntimeArtifactBindingRejectV1("runtime_artifact_role")
    path_before = _lstat_regular_source(source.source_path)
    try:
        descriptor = staging_io.open_trusted_source(
            source.source_path,
            trusted_root=trusted_source_root,
            trusted_uid=trusted_uid,
        )
    except JailerLauncherReject as exc:
        raise SpotV7RuntimeArtifactBindingRejectV1(
            "runtime_artifact_source_open"
        ) from exc
    try:
        opened_before = _fstat_descriptor(descriptor)
        if staging_io.file_version(path_before) != staging_io.file_version(opened_before):
            raise SpotV7RuntimeArtifactBindingRejectV1(
                "runtime_artifact_path_replaced"
            )
        if stat.S_IMODE(opened_before.st_mode) & 0o222:
            raise SpotV7RuntimeArtifactBindingRejectV1(
                "runtime_artifact_source_writable"
            )
        if opened_before.st_size != expected.size_bytes:
            raise SpotV7RuntimeArtifactBindingRejectV1(
                "runtime_artifact_size_mismatch"
            )
        digest = _hash_opened_artifact(descriptor, expected.size_bytes)
        opened_after = _fstat_descriptor(descriptor)
        if staging_io.file_version(opened_before) != staging_io.file_version(opened_after):
            raise SpotV7RuntimeArtifactBindingRejectV1(
                "runtime_artifact_changed_while_reading"
            )
        path_after = _lstat_regular_source(source.source_path)
        if staging_io.file_version(path_after) != staging_io.file_version(opened_after):
            raise SpotV7RuntimeArtifactBindingRejectV1(
                "runtime_artifact_path_replaced"
            )
        if digest != expected.sha256.hex():
            raise SpotV7RuntimeArtifactBindingRejectV1(
                "runtime_artifact_digest_mismatch"
            )
        return _OpenedRuntimeArtifactV1(
            role=source.role,
            source_path=source.source_path,
            descriptor=descriptor,
            version=staging_io.file_version(opened_after),
            expected_sha256=expected.sha256.hex(),
            expected_size=expected.size_bytes,
        )
    except BaseException:
        _close_descriptor(descriptor)
        raise


def _reverify_opened_artifact(record: _OpenedRuntimeArtifactV1) -> None:
    opened_before = _fstat_descriptor(record.descriptor)
    path_before = _lstat_regular_source(record.source_path)
    if staging_io.file_version(path_before) != staging_io.file_version(opened_before):
        raise SpotV7RuntimeArtifactBindingRejectV1("runtime_artifact_path_replaced")
    if staging_io.file_version(opened_before) != record.version:
        raise SpotV7RuntimeArtifactBindingRejectV1("runtime_artifact_source_changed")
    digest = _hash_opened_artifact(record.descriptor, record.expected_size)
    opened_after = _fstat_descriptor(record.descriptor)
    if staging_io.file_version(opened_before) != staging_io.file_version(opened_after):
        raise SpotV7RuntimeArtifactBindingRejectV1(
            "runtime_artifact_changed_while_reading"
        )
    path_after = _lstat_regular_source(record.source_path)
    if staging_io.file_version(path_after) != staging_io.file_version(opened_after):
        raise SpotV7RuntimeArtifactBindingRejectV1("runtime_artifact_path_replaced")
    if digest != record.expected_sha256:
        raise SpotV7RuntimeArtifactBindingRejectV1("runtime_artifact_digest_mismatch")


def _lstat_regular_source(path: Path) -> os.stat_result:
    try:
        metadata = path.lstat()
    except OSError as exc:
        raise SpotV7RuntimeArtifactBindingRejectV1(
            "runtime_artifact_source_open"
        ) from exc
    if not stat.S_ISREG(metadata.st_mode) or metadata.st_nlink != 1:
        raise SpotV7RuntimeArtifactBindingRejectV1("runtime_artifact_source_open")
    return metadata


def _hash_opened_artifact(descriptor: int, expected_size: int) -> str:
    try:
        return staging_io.sha256_fd(descriptor, expected_size)
    except (JailerLauncherReject, OSError) as exc:
        raise SpotV7RuntimeArtifactBindingRejectV1(
            "runtime_artifact_changed_while_reading"
        ) from exc


def _fstat_descriptor(descriptor: int) -> os.stat_result:
    try:
        return os.fstat(descriptor)
    except OSError as exc:
        raise SpotV7RuntimeArtifactBindingRejectV1(
            "runtime_artifact_descriptor_invalid"
        ) from exc


def _close_descriptor(descriptor: int) -> None:
    try:
        os.close(descriptor)
    except OSError:
        pass
