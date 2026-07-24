"""Bind one replayed current Spot V7 release to exact execution-manifest bytes.

The result is an authority-neutral, revision-bound observation.  It is stale as
soon as release state advances and cannot authorize proof execution, runtime,
settlement, or production.  A final consumer must repeat the exact release-state
comparison inside the transaction that applies economic effects.
"""

from __future__ import annotations

import hashlib
from typing import Final, NoReturn, SupportsIndex, final

from src.state.canonical import canonical_json_bytes, domain_sep_bytes, encode_bytes
from tools import zrpf_spot_v7_authenticated_release_state_store_v3 as store_v3
from tools import zrpf_spot_v7_execution_authority_manifest_v1 as authority

CURRENT_RELEASE_EXECUTION_OBSERVATION_SCHEMA_V1: Final = (
    "zenodex.zrpf.spot_v7.current_release_execution_observation.v1"
)
CURRENT_RELEASE_EXECUTION_OBSERVATION_HASH_DOMAIN_V1: Final = domain_sep_bytes(
    "zrpf_spot_v7_current_release_execution_observation",
    version=1,
)
MAX_CURRENT_RELEASE_CANDIDATE_BYTES_V1: Final = 256 * 1_024
MAX_CURRENT_RELEASE_EXECUTION_MANIFEST_BYTES_V1: Final = 64 * 1_024
MAX_U64_V1: Final = (1 << 64) - 1


class SpotV7CurrentReleaseExecutionBindingRejectV1(ValueError):
    """Stable fail-closed error at the current-release execution boundary."""

    def __init__(self, code: str, detail: str) -> None:
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}")


def _reject(code: str, detail: str) -> SpotV7CurrentReleaseExecutionBindingRejectV1:
    return SpotV7CurrentReleaseExecutionBindingRejectV1(code, detail)


class _CurrentReleaseExecutionBindingSealV1:
    __slots__ = ()


_CURRENT_RELEASE_EXECUTION_BINDING_SEAL_V1: Final = _CurrentReleaseExecutionBindingSealV1()


@final
class _AuthorityNeutralCurrentReleaseExecutionBindingV1:
    """Private retained observation with every authority property fixed false."""

    __slots__ = (
        "_canonical_observation_bytes",
        "_current_candidate_id",
        "_current_candidate_sha256",
        "_current_release_revision",
        "_current_select_input_id",
        "_database_revision",
        "_exact_authority_manifest_bytes",
        "_exact_candidate_bytes",
        "_execution_authority_manifest_sha256",
        "_last_evaluation_epoch",
        "_observation_root",
        "_release_state_root",
        "_store_identity_sha256",
    )
    _canonical_observation_bytes: bytes
    _current_candidate_id: bytes
    _current_candidate_sha256: bytes
    _current_release_revision: int
    _current_select_input_id: bytes
    _database_revision: int
    _exact_authority_manifest_bytes: bytes
    _exact_candidate_bytes: bytes
    _execution_authority_manifest_sha256: bytes
    _last_evaluation_epoch: int
    _observation_root: bytes
    _release_state_root: bytes
    _store_identity_sha256: bytes

    def __new__(cls) -> _AuthorityNeutralCurrentReleaseExecutionBindingV1:
        raise TypeError("current-release execution binding requires checked construction")

    @classmethod
    def _from_checked(
        cls,
        *,
        store_identity_sha256: bytes,
        database_revision: int,
        last_evaluation_epoch: int,
        release_state_root: bytes,
        current_candidate_id: bytes,
        current_candidate_sha256: bytes,
        current_release_revision: int,
        current_select_input_id: bytes,
        current_revocation_record_id: None,
        exact_candidate_bytes: bytes,
        exact_authority_manifest_bytes: bytes,
        execution_authority_manifest_sha256: bytes,
        seal: _CurrentReleaseExecutionBindingSealV1,
    ) -> _AuthorityNeutralCurrentReleaseExecutionBindingV1:
        if seal is not _CURRENT_RELEASE_EXECUTION_BINDING_SEAL_V1:
            raise TypeError("current-release execution binding requires the module-private seal")
        store_identity = _require_digest(
            store_identity_sha256,
            name="store_identity_sha256",
        )
        revision = _require_positive_u64(database_revision, name="database_revision")
        evaluation_epoch = _require_u64(
            last_evaluation_epoch,
            name="last_evaluation_epoch",
        )
        state_root = _require_digest(release_state_root, name="release_state_root")
        candidate_id = _require_digest(current_candidate_id, name="current_candidate_id")
        candidate_sha256 = _require_digest(
            current_candidate_sha256,
            name="current_candidate_sha256",
        )
        release_revision = _require_positive_u64(
            current_release_revision,
            name="current_release_revision",
        )
        select_input_id = _require_digest(
            current_select_input_id,
            name="current_select_input_id",
        )
        if current_revocation_record_id is not None:
            raise ValueError("current release must be nonrevoked")
        candidate_bytes = _require_bounded_bytes(
            exact_candidate_bytes,
            maximum=MAX_CURRENT_RELEASE_CANDIDATE_BYTES_V1,
            name="exact_candidate_bytes",
        )
        manifest_bytes = _require_bounded_bytes(
            exact_authority_manifest_bytes,
            maximum=MAX_CURRENT_RELEASE_EXECUTION_MANIFEST_BYTES_V1,
            name="exact_authority_manifest_bytes",
        )
        manifest_sha256 = _require_digest(
            execution_authority_manifest_sha256,
            name="execution_authority_manifest_sha256",
        )
        if hashlib.sha256(candidate_bytes).digest() != candidate_sha256:
            raise ValueError("exact candidate bytes do not match current candidate SHA-256")
        if hashlib.sha256(manifest_bytes).digest() != manifest_sha256:
            raise ValueError("exact authority manifest bytes do not match manifest SHA-256")
        observation_bytes = _canonical_observation_bytes(
            store_identity_sha256=store_identity,
            database_revision=revision,
            last_evaluation_epoch=evaluation_epoch,
            release_state_root=state_root,
            current_candidate_id=candidate_id,
            current_candidate_sha256=candidate_sha256,
            current_release_revision=release_revision,
            current_select_input_id=select_input_id,
            execution_authority_manifest_sha256=manifest_sha256,
            exact_candidate_bytes_sha256=hashlib.sha256(candidate_bytes).digest(),
            exact_authority_manifest_bytes_sha256=hashlib.sha256(manifest_bytes).digest(),
        )
        observation_root = _observation_root(observation_bytes)
        value = object.__new__(cls)
        object.__setattr__(value, "_store_identity_sha256", store_identity)
        object.__setattr__(value, "_database_revision", revision)
        object.__setattr__(value, "_last_evaluation_epoch", evaluation_epoch)
        object.__setattr__(value, "_release_state_root", state_root)
        object.__setattr__(value, "_current_candidate_id", candidate_id)
        object.__setattr__(value, "_current_candidate_sha256", candidate_sha256)
        object.__setattr__(value, "_current_release_revision", release_revision)
        object.__setattr__(value, "_current_select_input_id", select_input_id)
        object.__setattr__(value, "_exact_candidate_bytes", candidate_bytes)
        object.__setattr__(value, "_exact_authority_manifest_bytes", manifest_bytes)
        object.__setattr__(
            value,
            "_execution_authority_manifest_sha256",
            manifest_sha256,
        )
        object.__setattr__(value, "_canonical_observation_bytes", observation_bytes)
        object.__setattr__(value, "_observation_root", observation_root)
        return value

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("current-release execution binding cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("current-release execution binding is immutable")

    def __delattr__(self, _name: str) -> NoReturn:
        raise TypeError("current-release execution binding is immutable")

    def __copy__(self) -> NoReturn:
        raise TypeError("current-release execution binding cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("current-release execution binding cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("current-release execution binding cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("current-release execution binding cannot be serialized")

    def __getstate__(self) -> NoReturn:
        raise TypeError("current-release execution binding cannot be serialized")

    @property
    def store_identity_sha256(self) -> bytes:
        self._revalidated_observation()
        return self._store_identity_sha256

    @property
    def database_revision(self) -> int:
        self._revalidated_observation()
        return self._database_revision

    @property
    def last_evaluation_epoch(self) -> int:
        self._revalidated_observation()
        return self._last_evaluation_epoch

    @property
    def release_state_root(self) -> bytes:
        self._revalidated_observation()
        return self._release_state_root

    @property
    def current_candidate_id(self) -> bytes:
        self._revalidated_observation()
        return self._current_candidate_id

    @property
    def current_candidate_sha256(self) -> bytes:
        self._revalidated_observation()
        return self._current_candidate_sha256

    @property
    def current_release_revision(self) -> int:
        self._revalidated_observation()
        return self._current_release_revision

    @property
    def current_select_input_id(self) -> bytes:
        self._revalidated_observation()
        return self._current_select_input_id

    @property
    def current_revocation_record_id(self) -> None:
        self._revalidated_observation()
        return None

    @property
    def exact_candidate_bytes(self) -> bytes:
        self._revalidated_observation()
        return self._exact_candidate_bytes

    @property
    def exact_authority_manifest_bytes(self) -> bytes:
        self._revalidated_observation()
        return self._exact_authority_manifest_bytes

    @property
    def execution_authority_manifest_sha256(self) -> bytes:
        self._revalidated_observation()
        return self._execution_authority_manifest_sha256

    @property
    def canonical_observation_bytes(self) -> bytes:
        canonical, _ = self._revalidated_observation()
        return canonical

    @property
    def observation_root(self) -> bytes:
        _, root = self._revalidated_observation()
        return root

    @property
    def currentness_at_settlement_established(self) -> bool:
        return False

    @property
    def atomic_release_and_settlement_commit_established(self) -> bool:
        return False

    @property
    def external_monotonic_rollback_resistance_established(self) -> bool:
        return False

    @property
    def hostile_same_interpreter_resistance_established(self) -> bool:
        return False

    @property
    def proof_receipt_authority(self) -> bool:
        return False

    @property
    def runtime_authority(self) -> bool:
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

    def _revalidated_observation(self) -> tuple[bytes, bytes]:
        canonical = _canonical_observation_bytes(
            store_identity_sha256=self._store_identity_sha256,
            database_revision=self._database_revision,
            last_evaluation_epoch=self._last_evaluation_epoch,
            release_state_root=self._release_state_root,
            current_candidate_id=self._current_candidate_id,
            current_candidate_sha256=self._current_candidate_sha256,
            current_release_revision=self._current_release_revision,
            current_select_input_id=self._current_select_input_id,
            execution_authority_manifest_sha256=(self._execution_authority_manifest_sha256),
            exact_candidate_bytes_sha256=hashlib.sha256(self._exact_candidate_bytes).digest(),
            exact_authority_manifest_bytes_sha256=hashlib.sha256(
                self._exact_authority_manifest_bytes
            ).digest(),
        )
        root = _observation_root(canonical)
        if canonical != self._canonical_observation_bytes or root != self._observation_root:
            raise ValueError("current-release execution observation was mutated")
        return canonical, root


def bind_current_release_to_execution_manifest_v1(
    store: store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3,
    *,
    exact_authority_manifest_bytes: bytes,
) -> _AuthorityNeutralCurrentReleaseExecutionBindingV1:
    """Replay current release state and recheck exact candidate/manifest bytes once."""

    if type(store) is not store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3:
        raise TypeError("store must be the exact authenticated release-state V3 type")
    if type(exact_authority_manifest_bytes) is not bytes:
        raise TypeError("exact_authority_manifest_bytes must be exact bytes")
    try:
        snapshot = store._current_release_snapshot_for_execution_binding_v1()
    except store_v3.SpotV7AuthenticatedReleaseStateStoreErrorV3 as exc:
        raise _reject("CURRENT_RELEASE_SNAPSHOT_REJECTED", str(exc)) from exc
    if type(snapshot) is not store_v3._AuthorityNeutralCurrentReleaseSnapshotV1:
        raise _reject("CURRENT_RELEASE_SNAPSHOT_TYPE", "store returned an invalid snapshot type")
    candidate_bytes = snapshot.current_candidate_bytes
    candidate_sha256 = hashlib.sha256(candidate_bytes).digest()
    if candidate_sha256 != snapshot.current_candidate_sha256:
        raise _reject("CURRENT_CANDIDATE_SHA256_MISMATCH", "locked candidate bytes changed")
    try:
        checked = authority.check_exact_spot_v7_execution_authority_manifest_v1(
            exact_release_candidate_bytes=candidate_bytes,
            exact_authority_manifest_bytes=exact_authority_manifest_bytes,
        )
    except (authority.SpotV7ExecutionAuthorityManifestRejectV1, TypeError, ValueError) as exc:
        raise _reject("EXECUTION_MANIFEST_REJECTED", str(exc)) from exc
    if checked.candidate_id != snapshot.current_candidate_id:
        raise _reject("CURRENT_CANDIDATE_ID_MISMATCH", "checker candidate differs from store")
    if checked.candidate_manifest_sha256 != snapshot.current_candidate_sha256:
        raise _reject("CURRENT_CANDIDATE_SHA256_MISMATCH", "checker candidate differs from store")
    if checked.release_revision != snapshot.current_release_revision:
        raise _reject("CURRENT_RELEASE_REVISION_MISMATCH", "checker revision differs from store")
    manifest_sha256 = hashlib.sha256(exact_authority_manifest_bytes).digest()
    if checked.authority_manifest_sha256 != manifest_sha256:
        raise _reject("EXECUTION_MANIFEST_SHA256_MISMATCH", "checker manifest digest differs")
    try:
        return _AuthorityNeutralCurrentReleaseExecutionBindingV1._from_checked(
            store_identity_sha256=snapshot.store_identity_sha256,
            database_revision=snapshot.database_revision,
            last_evaluation_epoch=snapshot.last_evaluation_epoch,
            release_state_root=snapshot.state_root,
            current_candidate_id=snapshot.current_candidate_id,
            current_candidate_sha256=snapshot.current_candidate_sha256,
            current_release_revision=snapshot.current_release_revision,
            current_select_input_id=snapshot.current_select_input_id,
            current_revocation_record_id=snapshot.current_revocation_record_id,
            exact_candidate_bytes=candidate_bytes,
            exact_authority_manifest_bytes=exact_authority_manifest_bytes,
            execution_authority_manifest_sha256=manifest_sha256,
            seal=_CURRENT_RELEASE_EXECUTION_BINDING_SEAL_V1,
        )
    except (TypeError, ValueError) as exc:
        raise _reject("CURRENT_RELEASE_EXECUTION_BINDING_INVALID", str(exc)) from exc


def _canonical_observation_bytes(
    *,
    store_identity_sha256: bytes,
    database_revision: int,
    last_evaluation_epoch: int,
    release_state_root: bytes,
    current_candidate_id: bytes,
    current_candidate_sha256: bytes,
    current_release_revision: int,
    current_select_input_id: bytes,
    execution_authority_manifest_sha256: bytes,
    exact_candidate_bytes_sha256: bytes,
    exact_authority_manifest_bytes_sha256: bytes,
) -> bytes:
    document: dict[str, object] = {
        "current_candidate_id": _require_digest(
            current_candidate_id,
            name="current_candidate_id",
        ).hex(),
        "current_candidate_sha256": _require_digest(
            current_candidate_sha256,
            name="current_candidate_sha256",
        ).hex(),
        "current_release_revision": _require_positive_u64(
            current_release_revision,
            name="current_release_revision",
        ),
        "current_select_input_id": _require_digest(
            current_select_input_id,
            name="current_select_input_id",
        ).hex(),
        "database_revision": _require_positive_u64(
            database_revision,
            name="database_revision",
        ),
        "exact_authority_manifest_bytes_sha256": _require_digest(
            exact_authority_manifest_bytes_sha256,
            name="exact_authority_manifest_bytes_sha256",
        ).hex(),
        "exact_candidate_bytes_sha256": _require_digest(
            exact_candidate_bytes_sha256,
            name="exact_candidate_bytes_sha256",
        ).hex(),
        "execution_authority_manifest_sha256": _require_digest(
            execution_authority_manifest_sha256,
            name="execution_authority_manifest_sha256",
        ).hex(),
        "last_evaluation_epoch": _require_u64(
            last_evaluation_epoch,
            name="last_evaluation_epoch",
        ),
        "release_state_root": _require_digest(
            release_state_root,
            name="release_state_root",
        ).hex(),
        "schema": CURRENT_RELEASE_EXECUTION_OBSERVATION_SCHEMA_V1,
        "store_identity_hash": _require_digest(
            store_identity_sha256,
            name="store_identity_sha256",
        ).hex(),
    }
    return canonical_json_bytes(document) + b"\n"


def _observation_root(canonical_observation_bytes: bytes) -> bytes:
    return hashlib.sha256(
        CURRENT_RELEASE_EXECUTION_OBSERVATION_HASH_DOMAIN_V1
        + encode_bytes(canonical_observation_bytes)
    ).digest()


def _require_bounded_bytes(value: object, *, maximum: int, name: str) -> bytes:
    if type(value) is not bytes or not 0 < len(value) <= maximum:
        raise ValueError(f"{name} must be nonempty bounded bytes")
    return value


def _require_digest(value: object, *, name: str) -> bytes:
    if type(value) is not bytes or len(value) != 32 or not any(value):
        raise ValueError(f"{name} must be a nonzero 32-byte digest")
    return value


def _require_u64(value: object, *, name: str) -> int:
    if type(value) is not int or not 0 <= value <= MAX_U64_V1:
        raise ValueError(f"{name} must be a u64")
    return value


def _require_positive_u64(value: object, *, name: str) -> int:
    output = _require_u64(value, name=name)
    if output == 0:
        raise ValueError(f"{name} must be positive")
    return output


__all__ = [
    "CURRENT_RELEASE_EXECUTION_OBSERVATION_HASH_DOMAIN_V1",
    "CURRENT_RELEASE_EXECUTION_OBSERVATION_SCHEMA_V1",
    "SpotV7CurrentReleaseExecutionBindingRejectV1",
    "bind_current_release_to_execution_manifest_v1",
]
