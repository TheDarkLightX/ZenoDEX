"""Authority-neutral durable Spot V7 SELECT and REVOKE state V3.

The store accepts only the exact private capabilities minted by the governed
selection and revocation authentication adapters.  It independently replays
the complete retained BLS evidence before each transition and while opening or
reading the database.

This local history is internally replay-valid under one locally configured
identity, but it is not externally monotonic. A same-UID process can replace a
pathname or restore an older valid snapshot. The store therefore establishes
neither same-UID substitution resistance nor release, runtime, settlement, or
production authority.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import sqlite3
import stat
from contextlib import closing
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Any, Final, NoReturn, SupportsIndex, cast, final

from src.integration import zrpf_spot_v7_authenticated_release_revocation_v1 as revoke_auth
from src.integration import zrpf_spot_v7_authenticated_release_selection_v1 as select_auth
from src.integration._zrpf_spot_v7_release_revocation_envelope_v1 import (
    SPOT_V7_RELEASE_REVOCATION_PAYLOAD_KIND_V1,
    SpotV7ReleaseRevocationEnvelopeV1,
    parse_exact_spot_v7_release_revocation_envelope_v1,
)
from src.integration._zrpf_spot_v7_release_selection_envelope_v1 import (
    SPOT_V7_RELEASE_SELECTION_PAYLOAD_KIND_V1,
    SpotV7ReleaseSelectionEnvelopeV1,
    parse_exact_spot_v7_release_selection_envelope_v1,
)
from src.state.canonical import canonical_json_bytes
from tools.zrpf_spot_v7_governed_release_selector_input_v1 import (
    GovernedReleaseSelectorInputV1,
    SelectorOperationV1,
    SpotV7RevocationRecordV1,
    parse_exact_governed_release_selector_input_v1,
    parse_exact_spot_v7_revocation_record_v1,
)
from tools.zrpf_spot_v7_release_candidate_manifest_v1 import (
    SPOT_V7_RELEASE_PROFILE_V1,
    SpotV7ReleaseCandidateManifestV1,
    check_exact_spot_v7_release_candidate_manifest_v1,
)

STORE_SCHEMA_VERSION_V3: Final = 3
STORE_APPLICATION_ID_V3: Final = 0x5A525633
DEFAULT_BUSY_TIMEOUT_MS_V3: Final = 5_000
MAX_BUSY_TIMEOUT_MS_V3: Final = 60_000
MAX_AUTHENTICATED_RELEASE_EVENTS_V3: Final = 4_096
MAX_STORE_IDENTITY_BYTES_V3: Final = 32 * 1_024
MAX_AUTHENTICATION_EVIDENCE_BYTES_V3: Final = 2 * 1_024 * 1_024
MAX_CANDIDATE_BYTES_V3: Final = 256 * 1_024
MAX_ENVELOPE_BYTES_V3: Final = 32 * 1_024
MAX_SIGNER_REGISTRY_BYTES_V3: Final = 256 * 1_024
MAX_SIGNATURE_SET_BYTES_V3: Final = 1 * 1_024 * 1_024
MAX_QUORUM_REPORT_BYTES_V3: Final = 256 * 1_024
MAX_EXTERNAL_TRUST_PINS_BYTES_V3: Final = 32 * 1_024
MAX_U64_V3: Final = (1 << 64) - 1

SPOT_V7_AUTHENTICATED_RELEASE_STATE_STORE_IDENTITY_SCHEMA_V3: Final = (
    "zenodex.zrpf.spot_v7.authenticated_release_state_store_identity.v3"
)
SPOT_V7_AUTHENTICATED_RELEASE_STATE_MONOTONIC_ANCHOR_BLOCKER_V3: Final = (
    "EXTERNAL_MONOTONIC_RELEASE_STATE_ANCHOR_REQUIRED"
)
SPOT_V7_AUTHENTICATED_RELEASE_STATE_SAME_UID_BLOCKER_V3: Final = (
    "DEDICATED_UID_OR_DESCRIPTOR_BOUND_STORE_REQUIRED"
)
SPOT_V7_AUTHENTICATED_RELEASE_STATE_TRUST_ROOT_GOVERNANCE_BLOCKER_V3: Final = (
    "EXTERNAL_RELEASE_TRUST_ROOT_GOVERNANCE_REQUIRED"
)
SPOT_V7_DERIVED_STATIC_TRUST_PIN_IDENTITY_ALGORITHM_V3: Final = (
    "sha256-domain-canonical-static-pins-v3"
)
SPOT_V7_SELECTION_DERIVED_STATIC_TRUST_PIN_DOMAIN_V3: Final = (
    "zenodex.zrpf.spot_v7.selection_trust_pin_identity.v3"
)
SPOT_V7_REVOCATION_DERIVED_STATIC_TRUST_PIN_DOMAIN_V3: Final = (
    "zenodex.zrpf.spot_v7.revocation_trust_pin_identity.v3"
)

_GENESIS_STATE_DOMAIN_V3: Final = b"zenodex.zrpf.spot_v7.auth_release_state.genesis.v3"
_EVENT_STATE_DOMAIN_V3: Final = b"zenodex.zrpf.spot_v7.auth_release_state.event.v3"
_TOKEN_RE: Final = re.compile(r"^[A-Za-z0-9._:-]{1,128}$")
_ROOT_RE: Final = re.compile(r"^0x[0-9a-f]{64}$")


class _AuthorityNeutralClaimsV3:
    @property
    def release_governed_trust_roots_authenticated(self) -> bool:
        return False

    @property
    def release_governed_trust_roots_blocker_code(self) -> str:
        return SPOT_V7_AUTHENTICATED_RELEASE_STATE_TRUST_ROOT_GOVERNANCE_BLOCKER_V3

    @property
    def external_monotonic_state_anchor_verified(self) -> bool:
        return False

    @property
    def hostile_same_interpreter_resistance_established(self) -> bool:
        return False

    @property
    def same_uid_path_substitution_resistance_established(self) -> bool:
        return False

    @property
    def revocation_authority(self) -> bool:
        return False

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def runtime_authority(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


class _CurrentReleaseSnapshotSealV1:
    __slots__ = ()


_CURRENT_RELEASE_SNAPSHOT_SEAL_V1: Final = _CurrentReleaseSnapshotSealV1()


@final
class _AuthorityNeutralCurrentReleaseSnapshotV1(_AuthorityNeutralClaimsV3):
    """Fresh local current-release projection carrying no settlement authority."""

    __slots__ = (
        "_current_candidate_bytes",
        "_current_candidate_id",
        "_current_candidate_sha256",
        "_current_release_revision",
        "_current_revocation_record_id",
        "_current_select_input_id",
        "_database_revision",
        "_last_evaluation_epoch",
        "_state_root",
        "_store_identity_sha256",
    )
    _current_candidate_bytes: bytes
    _current_candidate_id: bytes
    _current_candidate_sha256: bytes
    _current_release_revision: int
    _current_revocation_record_id: None
    _current_select_input_id: bytes
    _database_revision: int
    _last_evaluation_epoch: int
    _state_root: bytes
    _store_identity_sha256: bytes

    def __new__(cls) -> _AuthorityNeutralCurrentReleaseSnapshotV1:
        raise TypeError("current-release snapshot requires verified store replay")

    @classmethod
    def _from_verified(
        cls,
        *,
        store_identity_sha256: bytes,
        database_revision: int,
        last_evaluation_epoch: int,
        state_root: bytes,
        current_candidate_id: bytes,
        current_candidate_sha256: bytes,
        current_release_revision: int,
        current_select_input_id: bytes,
        current_revocation_record_id: None,
        current_candidate_bytes: bytes,
        seal: _CurrentReleaseSnapshotSealV1,
    ) -> _AuthorityNeutralCurrentReleaseSnapshotV1:
        if seal is not _CURRENT_RELEASE_SNAPSHOT_SEAL_V1:
            raise TypeError("current-release snapshot requires the module-private seal")
        identity = _require_digest(
            store_identity_sha256,
            name="snapshot.store_identity_sha256",
        )
        revision = _require_positive_u64(
            database_revision,
            name="snapshot.database_revision",
        )
        evaluation_epoch = _require_u64(
            last_evaluation_epoch,
            name="snapshot.last_evaluation_epoch",
        )
        root = _require_digest(state_root, name="snapshot.state_root")
        candidate_id = _require_digest(
            current_candidate_id,
            name="snapshot.current_candidate_id",
        )
        candidate_sha256 = _require_digest(
            current_candidate_sha256,
            name="snapshot.current_candidate_sha256",
        )
        release_revision = _require_positive_u64(
            current_release_revision,
            name="snapshot.current_release_revision",
        )
        select_input_id = _require_digest(
            current_select_input_id,
            name="snapshot.current_select_input_id",
        )
        if current_revocation_record_id is not None:
            raise ValueError("current-release snapshot must be nonrevoked")
        if (
            type(current_candidate_bytes) is not bytes
            or not current_candidate_bytes
            or len(current_candidate_bytes) > MAX_CANDIDATE_BYTES_V3
        ):
            raise ValueError("snapshot.current_candidate_bytes are invalid")
        value = object.__new__(cls)
        object.__setattr__(value, "_store_identity_sha256", identity)
        object.__setattr__(value, "_database_revision", revision)
        object.__setattr__(value, "_last_evaluation_epoch", evaluation_epoch)
        object.__setattr__(value, "_state_root", root)
        object.__setattr__(value, "_current_candidate_id", candidate_id)
        object.__setattr__(value, "_current_candidate_sha256", candidate_sha256)
        object.__setattr__(value, "_current_release_revision", release_revision)
        object.__setattr__(value, "_current_select_input_id", select_input_id)
        object.__setattr__(value, "_current_revocation_record_id", None)
        object.__setattr__(value, "_current_candidate_bytes", current_candidate_bytes)
        return value

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("current-release snapshot cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("current-release snapshot is immutable")

    def __delattr__(self, _name: str) -> NoReturn:
        raise TypeError("current-release snapshot is immutable")

    def __copy__(self) -> NoReturn:
        raise TypeError("current-release snapshot cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("current-release snapshot cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("current-release snapshot cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("current-release snapshot cannot be serialized")

    def __getstate__(self) -> NoReturn:
        raise TypeError("current-release snapshot cannot be serialized")

    @property
    def store_identity_sha256(self) -> bytes:
        return self._store_identity_sha256

    @property
    def database_revision(self) -> int:
        return self._database_revision

    @property
    def last_evaluation_epoch(self) -> int:
        return self._last_evaluation_epoch

    @property
    def state_root(self) -> bytes:
        return self._state_root

    @property
    def current_candidate_id(self) -> bytes:
        return self._current_candidate_id

    @property
    def current_candidate_sha256(self) -> bytes:
        return self._current_candidate_sha256

    @property
    def current_release_revision(self) -> int:
        return self._current_release_revision

    @property
    def current_select_input_id(self) -> bytes:
        return self._current_select_input_id

    @property
    def current_revocation_record_id(self) -> None:
        return self._current_revocation_record_id

    @property
    def current_candidate_bytes(self) -> bytes:
        return self._current_candidate_bytes

    @property
    def currentness_at_settlement_verified(self) -> bool:
        return False

    @property
    def atomic_release_settlement_established(self) -> bool:
        return False

    @property
    def valid_snapshot_rollback_resistance_established(self) -> bool:
        return False


class SpotV7AuthenticatedReleaseStateStoreErrorV3(
    _AuthorityNeutralClaimsV3,
    ValueError,
):
    def __init__(self, code: str, detail: str) -> None:
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}")


class SpotV7AuthenticatedReleaseStateDurabilityUncertainV3(
    _AuthorityNeutralClaimsV3,
    RuntimeError,
):
    def __init__(self, *, selector_input_id: bytes, detail: str) -> None:
        self.selector_input_id = _require_digest(
            selector_input_id,
            name="selector_input_id",
        )
        self.detail = detail
        super().__init__(f"DURABILITY_OUTCOME_UNCERTAIN: {detail}")


class _TransitionRejectV3(ValueError):
    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(code)


class ReleaseStateEventKindV3(str, Enum):
    SELECT = "SELECT"
    REVOKE = "REVOKE"


class AuthenticatedReleaseStateDispositionV3(str, Enum):
    COMMITTED = "committed"
    IDEMPOTENT = "idempotent"
    REJECTED = "rejected"


@final
@dataclass(frozen=True, slots=True)
class SpotV7AuthenticatedReleaseStateStoreIdentityV3(_AuthorityNeutralClaimsV3):
    application_id: str
    chain_id: str
    domain_id: str
    release_profile: str
    selection_signer_registry_id: str
    selection_signer_registry_hash: str
    selection_signer_registry_revision: int
    selection_signer_registry_activation_epoch: int
    selection_signer_registry_revocation_epoch: int | None
    selection_quorum_threshold: int
    selection_derived_static_trust_pin_identity: bytes
    revocation_signer_registry_id: str
    revocation_signer_registry_hash: str
    revocation_signer_registry_revision: int
    revocation_signer_registry_activation_epoch: int
    revocation_signer_registry_revocation_epoch: int | None
    revocation_quorum_threshold: int
    revocation_derived_static_trust_pin_identity: bytes
    rollback_policy_root: bytes
    revocation_policy_root: bytes
    revocation_registry_root: bytes

    def __post_init__(self) -> None:
        for name in (
            "application_id",
            "chain_id",
            "domain_id",
            "release_profile",
            "selection_signer_registry_id",
            "revocation_signer_registry_id",
        ):
            _require_token(getattr(self, name), name=name)
        if self.release_profile != SPOT_V7_RELEASE_PROFILE_V1:
            raise ValueError("Spot V7 release profile required")
        if self.chain_id == self.domain_id:
            raise ValueError("chain and domain identifiers must differ")
        for prefix in ("selection", "revocation"):
            _require_root(
                getattr(self, f"{prefix}_signer_registry_hash"),
                name=f"{prefix}_signer_registry_hash",
            )
            _require_positive_u64(
                getattr(self, f"{prefix}_signer_registry_revision"),
                name=f"{prefix}_signer_registry_revision",
            )
            activation = _require_u64(
                getattr(self, f"{prefix}_signer_registry_activation_epoch"),
                name=f"{prefix}_signer_registry_activation_epoch",
            )
            revocation = _require_optional_u64(
                getattr(self, f"{prefix}_signer_registry_revocation_epoch"),
                name=f"{prefix}_signer_registry_revocation_epoch",
            )
            if revocation is not None and revocation <= activation:
                raise ValueError(f"{prefix} signer revocation must follow activation")
            _require_positive_u64(
                getattr(self, f"{prefix}_quorum_threshold"),
                name=f"{prefix}_quorum_threshold",
            )
            _require_digest(
                getattr(self, f"{prefix}_derived_static_trust_pin_identity"),
                name=f"{prefix}_derived_static_trust_pin_identity",
            )
        if self.selection_signer_registry_hash == self.revocation_signer_registry_hash:
            raise ValueError("selection and revocation signer-registry hashes must differ")
        _require_digest(self.rollback_policy_root, name="rollback_policy_root")
        _require_digest(self.revocation_policy_root, name="revocation_policy_root")
        _require_digest(self.revocation_registry_root, name="revocation_registry_root")

    @property
    def canonical_bytes(self) -> bytes:
        return canonical_json_bytes(
            {
                "application_id": self.application_id,
                "chain_id": self.chain_id,
                "domain_id": self.domain_id,
                "external_monotonic_state_anchor_verified": False,
                "hostile_same_interpreter_resistance_established": False,
                "production_authority": False,
                "release_authority": False,
                "release_governed_trust_roots_authenticated": False,
                "release_profile": self.release_profile,
                "revocation_authority": False,
                "revocation_derived_static_trust_pin_domain": (
                    SPOT_V7_REVOCATION_DERIVED_STATIC_TRUST_PIN_DOMAIN_V3
                ),
                "revocation_derived_static_trust_pin_identity": _root_text(
                    self.revocation_derived_static_trust_pin_identity
                ),
                "revocation_derived_static_trust_pin_identity_algorithm": (
                    SPOT_V7_DERIVED_STATIC_TRUST_PIN_IDENTITY_ALGORITHM_V3
                ),
                "revocation_policy_root": _root_text(self.revocation_policy_root),
                "revocation_quorum_threshold": self.revocation_quorum_threshold,
                "revocation_registry_root": _root_text(self.revocation_registry_root),
                "revocation_signer_registry_activation_epoch": (
                    self.revocation_signer_registry_activation_epoch
                ),
                "revocation_signer_registry_hash": self.revocation_signer_registry_hash,
                "revocation_signer_registry_id": self.revocation_signer_registry_id,
                "revocation_signer_registry_revision": (self.revocation_signer_registry_revision),
                "revocation_signer_registry_revocation_epoch": (
                    self.revocation_signer_registry_revocation_epoch
                ),
                "rollback_policy_root": _root_text(self.rollback_policy_root),
                "runtime_authority": False,
                "same_uid_path_substitution_resistance_established": False,
                "schema": SPOT_V7_AUTHENTICATED_RELEASE_STATE_STORE_IDENTITY_SCHEMA_V3,
                "selection_derived_static_trust_pin_domain": (
                    SPOT_V7_SELECTION_DERIVED_STATIC_TRUST_PIN_DOMAIN_V3
                ),
                "selection_derived_static_trust_pin_identity": _root_text(
                    self.selection_derived_static_trust_pin_identity
                ),
                "selection_derived_static_trust_pin_identity_algorithm": (
                    SPOT_V7_DERIVED_STATIC_TRUST_PIN_IDENTITY_ALGORITHM_V3
                ),
                "selection_quorum_threshold": self.selection_quorum_threshold,
                "selection_signer_registry_activation_epoch": (
                    self.selection_signer_registry_activation_epoch
                ),
                "selection_signer_registry_hash": self.selection_signer_registry_hash,
                "selection_signer_registry_id": self.selection_signer_registry_id,
                "selection_signer_registry_revision": self.selection_signer_registry_revision,
                "selection_signer_registry_revocation_epoch": (
                    self.selection_signer_registry_revocation_epoch
                ),
                "settlement_authority": False,
            }
        )

    @property
    def identity_sha256(self) -> bytes:
        return hashlib.sha256(self.canonical_bytes).digest()


@final
@dataclass(frozen=True, slots=True)
class SpotV7AuthenticatedReleaseStateCursorV3(_AuthorityNeutralClaimsV3):
    database_revision: int
    state_root: bytes
    last_evaluation_epoch: int | None
    current_candidate_id: bytes | None
    current_candidate_sha256: bytes | None
    current_release_revision: int | None
    current_select_input_id: bytes | None
    current_revoked: bool
    current_revocation_record_id: bytes | None

    def __post_init__(self) -> None:
        _require_u64(self.database_revision, name="database_revision")
        _require_digest(self.state_root, name="state_root")
        _require_optional_u64(self.last_evaluation_epoch, name="last_evaluation_epoch")
        if type(self.current_revoked) is not bool:
            raise TypeError("current_revoked must be bool")
        values = (
            self.last_evaluation_epoch,
            self.current_candidate_id,
            self.current_candidate_sha256,
            self.current_release_revision,
            self.current_select_input_id,
        )
        if self.database_revision == 0:
            if any(value is not None for value in values) or self.current_revoked:
                raise ValueError("genesis cursor must be empty and not revoked")
        else:
            if any(value is None for value in values):
                raise ValueError("non-genesis cursor requires one complete current candidate")
            _require_digest(self.current_candidate_id, name="current_candidate_id")
            _require_digest(self.current_candidate_sha256, name="current_candidate_sha256")
            _require_positive_u64(self.current_release_revision, name="current_release_revision")
            _require_digest(self.current_select_input_id, name="current_select_input_id")
        if self.current_revoked != (self.current_revocation_record_id is not None):
            raise ValueError("revoked cursor and revocation-record ID disagree")
        if self.current_revocation_record_id is not None:
            _require_digest(
                self.current_revocation_record_id,
                name="current_revocation_record_id",
            )


class _ReleaseStateResultSealV3:
    __slots__ = ()


_RELEASE_STATE_RESULT_SEAL_V3: Final = _ReleaseStateResultSealV3()


@final
class SpotV7AuthenticatedReleaseStateResultV3(_AuthorityNeutralClaimsV3):
    """Opaque authority-neutral status returned only by the replayed store."""

    __slots__ = ("_code", "_cursor", "_disposition", "_event_kind", "_selector_input_id")
    _code: str
    _cursor: SpotV7AuthenticatedReleaseStateCursorV3
    _disposition: AuthenticatedReleaseStateDispositionV3
    _event_kind: ReleaseStateEventKindV3
    _selector_input_id: bytes

    def __new__(cls, *_args: object, **_kwargs: object) -> SpotV7AuthenticatedReleaseStateResultV3:
        raise TypeError("release-state status requires the module-private store result seal")

    @classmethod
    def _from_store(
        cls,
        *,
        disposition: AuthenticatedReleaseStateDispositionV3,
        code: str,
        event_kind: ReleaseStateEventKindV3,
        selector_input_id: bytes,
        cursor: SpotV7AuthenticatedReleaseStateCursorV3,
        seal: _ReleaseStateResultSealV3,
    ) -> SpotV7AuthenticatedReleaseStateResultV3:
        if seal is not _RELEASE_STATE_RESULT_SEAL_V3:
            raise TypeError("release-state status requires the module-private store result seal")
        if type(disposition) is not AuthenticatedReleaseStateDispositionV3:
            raise TypeError("release-state disposition must use the exact V3 enum")
        normalized_code = _require_token(code, name="release_state_result.code")
        if type(event_kind) is not ReleaseStateEventKindV3:
            raise TypeError("release-state event kind must use the exact V3 enum")
        selector_id = _require_digest(
            selector_input_id,
            name="release_state_result.selector_input_id",
        )
        if type(cursor) is not SpotV7AuthenticatedReleaseStateCursorV3:
            raise TypeError("release-state result cursor must use the exact V3 cursor")
        value = object.__new__(cls)
        object.__setattr__(value, "_disposition", disposition)
        object.__setattr__(value, "_code", normalized_code)
        object.__setattr__(value, "_event_kind", event_kind)
        object.__setattr__(value, "_selector_input_id", selector_id)
        object.__setattr__(value, "_cursor", cursor)
        return value

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("release-state status cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("release-state status is immutable")

    def __delattr__(self, _name: str) -> NoReturn:
        raise TypeError("release-state status is immutable")

    def __bool__(self) -> NoReturn:
        raise TypeError("release-state status requires explicit disposition handling")

    def __copy__(self) -> NoReturn:
        raise TypeError("release-state status cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("release-state status cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("release-state status cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("release-state status cannot be serialized")

    def __getstate__(self) -> NoReturn:
        raise TypeError("release-state status cannot be serialized")

    @property
    def disposition(self) -> AuthenticatedReleaseStateDispositionV3:
        return self._disposition

    @property
    def code(self) -> str:
        return self._code

    @property
    def event_kind(self) -> ReleaseStateEventKindV3:
        return self._event_kind

    @property
    def selector_input_id(self) -> bytes:
        return self._selector_input_id

    @property
    def cursor(self) -> SpotV7AuthenticatedReleaseStateCursorV3:
        return self._cursor


@dataclass(frozen=True, slots=True)
class _AuthenticatedEventArtifactsV3:
    event_kind: ReleaseStateEventKindV3
    selector: GovernedReleaseSelectorInputV1
    candidate: SpotV7ReleaseCandidateManifestV1
    candidate_bytes: bytes
    selector_input_bytes: bytes
    envelope_bytes: bytes
    record: SpotV7RevocationRecordV1 | None
    record_bytes: bytes | None
    signer_registry_bytes: bytes
    signature_envelopes_bytes: bytes
    quorum_report_bytes: bytes
    external_trust_pins_bytes: bytes
    authentication_evidence_bytes: bytes
    parent_candidate_id: bytes | None
    activation_epoch: int
    expiration_epoch: int | None
    selection_envelope: SpotV7ReleaseSelectionEnvelopeV1 | None
    revocation_envelope: SpotV7ReleaseRevocationEnvelopeV1 | None
    pins: object

    @property
    def selector_input_id(self) -> bytes:
        return self.selector.input_id

    @property
    def candidate_sha256(self) -> bytes:
        return hashlib.sha256(self.candidate_bytes).digest()

    @property
    def release_revision(self) -> int:
        return self.candidate.release_revision

    @property
    def evaluation_epoch(self) -> int:
        return self.selector.evaluation_epoch

    @property
    def authentication_evidence_sha256(self) -> bytes:
        return hashlib.sha256(self.authentication_evidence_bytes).digest()

    @property
    def revocation_record_id(self) -> bytes | None:
        return None if self.record is None else self.record.record_id


_SCHEMA_STATEMENTS_V3: Final = (
    """
    CREATE TABLE spot_v7_authenticated_release_state_meta_v3 (
        singleton INTEGER NOT NULL PRIMARY KEY CHECK (singleton = 1),
        schema_version INTEGER NOT NULL CHECK (schema_version = 3),
        store_identity_bytes BLOB NOT NULL CHECK (typeof(store_identity_bytes) = 'blob' AND length(store_identity_bytes) BETWEEN 1 AND 32768),
        store_identity_sha256 BLOB NOT NULL CHECK (typeof(store_identity_sha256) = 'blob' AND length(store_identity_sha256) = 32),
        database_revision_be BLOB NOT NULL CHECK (typeof(database_revision_be) = 'blob' AND length(database_revision_be) = 8),
        state_root BLOB NOT NULL CHECK (typeof(state_root) = 'blob' AND length(state_root) = 32),
        event_count INTEGER NOT NULL CHECK (event_count BETWEEN 0 AND 4096),
        last_evaluation_epoch_be BLOB CHECK (last_evaluation_epoch_be IS NULL OR (typeof(last_evaluation_epoch_be) = 'blob' AND length(last_evaluation_epoch_be) = 8)),
        current_candidate_id BLOB CHECK (current_candidate_id IS NULL OR (typeof(current_candidate_id) = 'blob' AND length(current_candidate_id) = 32)),
        current_candidate_sha256 BLOB CHECK (current_candidate_sha256 IS NULL OR (typeof(current_candidate_sha256) = 'blob' AND length(current_candidate_sha256) = 32)),
        current_release_revision_be BLOB CHECK (current_release_revision_be IS NULL OR (typeof(current_release_revision_be) = 'blob' AND length(current_release_revision_be) = 8)),
        current_select_input_id BLOB CHECK (current_select_input_id IS NULL OR (typeof(current_select_input_id) = 'blob' AND length(current_select_input_id) = 32)),
        current_revoked INTEGER NOT NULL CHECK (current_revoked IN (0, 1)),
        current_revocation_record_id BLOB CHECK (current_revocation_record_id IS NULL OR (typeof(current_revocation_record_id) = 'blob' AND length(current_revocation_record_id) = 32)),
        release_governed_trust_roots_authenticated INTEGER NOT NULL CHECK (release_governed_trust_roots_authenticated = 0),
        external_monotonic_state_anchor_verified INTEGER NOT NULL CHECK (external_monotonic_state_anchor_verified = 0),
        hostile_same_interpreter_resistance_established INTEGER NOT NULL CHECK (hostile_same_interpreter_resistance_established = 0),
        same_uid_path_substitution_resistance_established INTEGER NOT NULL CHECK (same_uid_path_substitution_resistance_established = 0),
        revocation_authority INTEGER NOT NULL CHECK (revocation_authority = 0),
        release_authority INTEGER NOT NULL CHECK (release_authority = 0),
        runtime_authority INTEGER NOT NULL CHECK (runtime_authority = 0),
        settlement_authority INTEGER NOT NULL CHECK (settlement_authority = 0),
        production_authority INTEGER NOT NULL CHECK (production_authority = 0),
        CHECK (current_revoked = (current_revocation_record_id IS NOT NULL)),
        CHECK (
            (event_count = 0 AND last_evaluation_epoch_be IS NULL AND current_candidate_id IS NULL AND current_candidate_sha256 IS NULL AND current_release_revision_be IS NULL AND current_select_input_id IS NULL AND current_revoked = 0)
            OR
            (event_count > 0 AND last_evaluation_epoch_be IS NOT NULL AND current_candidate_id IS NOT NULL AND current_candidate_sha256 IS NOT NULL AND current_release_revision_be IS NOT NULL AND current_select_input_id IS NOT NULL)
        )
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE spot_v7_authenticated_release_state_events_v3 (
        event_revision_be BLOB NOT NULL PRIMARY KEY CHECK (typeof(event_revision_be) = 'blob' AND length(event_revision_be) = 8),
        event_kind TEXT NOT NULL CHECK (event_kind IN ('SELECT', 'REVOKE')),
        selector_input_id BLOB NOT NULL UNIQUE CHECK (typeof(selector_input_id) = 'blob' AND length(selector_input_id) = 32),
        selector_input_bytes BLOB NOT NULL CHECK (typeof(selector_input_bytes) = 'blob' AND length(selector_input_bytes) = 320),
        candidate_id BLOB NOT NULL CHECK (typeof(candidate_id) = 'blob' AND length(candidate_id) = 32),
        candidate_sha256 BLOB NOT NULL CHECK (typeof(candidate_sha256) = 'blob' AND length(candidate_sha256) = 32),
        candidate_bytes BLOB NOT NULL CHECK (typeof(candidate_bytes) = 'blob' AND length(candidate_bytes) BETWEEN 1 AND 262144),
        release_revision_be BLOB NOT NULL CHECK (typeof(release_revision_be) = 'blob' AND length(release_revision_be) = 8),
        evaluation_epoch_be BLOB NOT NULL CHECK (typeof(evaluation_epoch_be) = 'blob' AND length(evaluation_epoch_be) = 8),
        envelope_bytes BLOB NOT NULL CHECK (typeof(envelope_bytes) = 'blob' AND length(envelope_bytes) BETWEEN 1 AND 32768),
        revocation_record_bytes BLOB CHECK (revocation_record_bytes IS NULL OR (typeof(revocation_record_bytes) = 'blob' AND length(revocation_record_bytes) = 216)),
        revocation_record_id BLOB UNIQUE CHECK (revocation_record_id IS NULL OR (typeof(revocation_record_id) = 'blob' AND length(revocation_record_id) = 32)),
        signer_registry_bytes BLOB NOT NULL CHECK (typeof(signer_registry_bytes) = 'blob' AND length(signer_registry_bytes) BETWEEN 1 AND 262144),
        signature_envelopes_bytes BLOB NOT NULL CHECK (typeof(signature_envelopes_bytes) = 'blob' AND length(signature_envelopes_bytes) BETWEEN 1 AND 1048576),
        quorum_report_bytes BLOB NOT NULL CHECK (typeof(quorum_report_bytes) = 'blob' AND length(quorum_report_bytes) BETWEEN 1 AND 262144),
        external_trust_pins_bytes BLOB NOT NULL CHECK (typeof(external_trust_pins_bytes) = 'blob' AND length(external_trust_pins_bytes) BETWEEN 1 AND 32768),
        derived_static_trust_pin_identity BLOB NOT NULL CHECK (typeof(derived_static_trust_pin_identity) = 'blob' AND length(derived_static_trust_pin_identity) = 32),
        authentication_evidence_bytes BLOB NOT NULL CHECK (typeof(authentication_evidence_bytes) = 'blob' AND length(authentication_evidence_bytes) BETWEEN 1 AND 2097152),
        authentication_evidence_sha256 BLOB NOT NULL UNIQUE CHECK (typeof(authentication_evidence_sha256) = 'blob' AND length(authentication_evidence_sha256) = 32),
        select_candidate_id BLOB UNIQUE CHECK (select_candidate_id IS NULL OR (typeof(select_candidate_id) = 'blob' AND length(select_candidate_id) = 32)),
        select_release_revision_be BLOB UNIQUE CHECK (select_release_revision_be IS NULL OR (typeof(select_release_revision_be) = 'blob' AND length(select_release_revision_be) = 8)),
        revoke_candidate_id BLOB UNIQUE CHECK (revoke_candidate_id IS NULL OR (typeof(revoke_candidate_id) = 'blob' AND length(revoke_candidate_id) = 32)),
        revoke_release_revision_be BLOB UNIQUE CHECK (revoke_release_revision_be IS NULL OR (typeof(revoke_release_revision_be) = 'blob' AND length(revoke_release_revision_be) = 8)),
        previous_state_root BLOB NOT NULL CHECK (typeof(previous_state_root) = 'blob' AND length(previous_state_root) = 32),
        result_state_root BLOB NOT NULL UNIQUE CHECK (typeof(result_state_root) = 'blob' AND length(result_state_root) = 32),
        durable_authenticated_release_state_recorded INTEGER NOT NULL CHECK (durable_authenticated_release_state_recorded = 1),
        release_governed_trust_roots_authenticated INTEGER NOT NULL CHECK (release_governed_trust_roots_authenticated = 0),
        external_monotonic_state_anchor_verified INTEGER NOT NULL CHECK (external_monotonic_state_anchor_verified = 0),
        hostile_same_interpreter_resistance_established INTEGER NOT NULL CHECK (hostile_same_interpreter_resistance_established = 0),
        same_uid_path_substitution_resistance_established INTEGER NOT NULL CHECK (same_uid_path_substitution_resistance_established = 0),
        revocation_authority INTEGER NOT NULL CHECK (revocation_authority = 0),
        release_authority INTEGER NOT NULL CHECK (release_authority = 0),
        runtime_authority INTEGER NOT NULL CHECK (runtime_authority = 0),
        settlement_authority INTEGER NOT NULL CHECK (settlement_authority = 0),
        production_authority INTEGER NOT NULL CHECK (production_authority = 0),
        CHECK (
            (event_kind = 'SELECT' AND revocation_record_bytes IS NULL AND revocation_record_id IS NULL AND select_candidate_id = candidate_id AND select_release_revision_be = release_revision_be AND revoke_candidate_id IS NULL AND revoke_release_revision_be IS NULL)
            OR
            (event_kind = 'REVOKE' AND revocation_record_bytes IS NOT NULL AND revocation_record_id IS NOT NULL AND select_candidate_id IS NULL AND select_release_revision_be IS NULL AND revoke_candidate_id = candidate_id AND revoke_release_revision_be = release_revision_be)
        )
    ) STRICT, WITHOUT ROWID
    """,
)


def _schema_name(statement: str) -> str:
    words = statement.split()
    return words[2]


_EXPECTED_SCHEMA_SQL_V3: Final = {
    _schema_name(statement): statement for statement in _SCHEMA_STATEMENTS_V3
}


@final
class SQLiteSpotV7AuthenticatedReleaseStateStoreV3(_AuthorityNeutralClaimsV3):
    """Fsync-backed local SELECT/REVOKE history with no authority mint."""

    __slots__ = ("_busy_timeout_ms", "_identity", "_path")

    def __init__(
        self,
        path: Path,
        *,
        identity: SpotV7AuthenticatedReleaseStateStoreIdentityV3,
        busy_timeout_ms: int = DEFAULT_BUSY_TIMEOUT_MS_V3,
    ) -> None:
        _validate_store_path(path, busy_timeout_ms)
        if type(identity) is not SpotV7AuthenticatedReleaseStateStoreIdentityV3:
            raise TypeError("store identity must be the exact V3 identity type")
        self._path = path
        self._identity = identity
        self._busy_timeout_ms = busy_timeout_ms
        created = _create_private_database_file(path)
        try:
            with closing(self._connect()) as connection:
                connection.execute("BEGIN EXCLUSIVE")
                try:
                    _initialize_or_validate(connection, identity)
                    connection.commit()
                except (sqlite3.Error, TypeError, ValueError):
                    if connection.in_transaction:
                        connection.rollback()
                    raise
            if created:
                _fsync_directory(path.parent)
        except (OSError, sqlite3.Error, TypeError, ValueError) as exc:
            raise SpotV7AuthenticatedReleaseStateStoreErrorV3(
                "STORE_OPEN_FAILED",
                str(exc),
            ) from exc

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("SQLiteSpotV7AuthenticatedReleaseStateStoreV3 cannot be subclassed")

    @property
    def path(self) -> Path:
        return self._path

    @property
    def identity(self) -> SpotV7AuthenticatedReleaseStateStoreIdentityV3:
        return self._identity

    @property
    def monotonic_state_anchor_blocker_code(self) -> str:
        return SPOT_V7_AUTHENTICATED_RELEASE_STATE_MONOTONIC_ANCHOR_BLOCKER_V3

    @property
    def same_uid_path_substitution_blocker_code(self) -> str:
        return SPOT_V7_AUTHENTICATED_RELEASE_STATE_SAME_UID_BLOCKER_V3

    def read_cursor(self) -> SpotV7AuthenticatedReleaseStateCursorV3:
        connection: sqlite3.Connection | None = None
        try:
            connection = self._connect()
            connection.execute("BEGIN")
            _validate_schema(connection)
            cursor = _validate_complete_history(connection, self._identity)
            connection.rollback()
            return cursor
        except (OSError, sqlite3.Error, TypeError, ValueError) as exc:
            if connection is not None and connection.in_transaction:
                connection.rollback()
            raise SpotV7AuthenticatedReleaseStateStoreErrorV3(
                "STORE_READ_FAILED",
                str(exc),
            ) from exc
        finally:
            if connection is not None:
                connection.close()

    def _release_state_cursor_history_for_checkpoint_v1(
        self,
    ) -> tuple[SpotV7AuthenticatedReleaseStateCursorV3, ...]:
        """Replay and return every exact cursor under one read transaction."""

        connection: sqlite3.Connection | None = None
        try:
            connection = self._connect()
            connection.execute("BEGIN")
            _validate_schema(connection)
            cursors = _validate_complete_history_chain(connection, self._identity)
            connection.rollback()
            return cursors
        except (OSError, sqlite3.Error, TypeError, ValueError) as exc:
            if connection is not None and connection.in_transaction:
                connection.rollback()
            raise SpotV7AuthenticatedReleaseStateStoreErrorV3(
                "CHECKPOINT_HISTORY_READ_FAILED",
                str(exc),
            ) from exc
        finally:
            if connection is not None:
                connection.close()

    def _current_release_snapshot_for_execution_binding_v1(
        self,
    ) -> _AuthorityNeutralCurrentReleaseSnapshotV1:
        """Replay under a write lock and project one local nonrevoked release."""

        connection: sqlite3.Connection | None = None
        try:
            connection = self._connect()
            connection.execute("BEGIN IMMEDIATE")
            _validate_schema(connection)
            cursor = _validate_complete_history(connection, self._identity)
            snapshot = _build_current_release_snapshot(
                connection,
                self._identity,
                cursor,
            )
            connection.rollback()
            return snapshot
        except (OSError, sqlite3.Error, TypeError, ValueError) as exc:
            if connection is not None and connection.in_transaction:
                connection.rollback()
            raise SpotV7AuthenticatedReleaseStateStoreErrorV3(
                "CURRENT_RELEASE_SNAPSHOT_FAILED",
                str(exc),
            ) from exc
        finally:
            if connection is not None:
                connection.close()

    def commit_selection(
        self,
        capability: select_auth._AuthenticatedSpotV7ReleaseSelectionV1,
    ) -> SpotV7AuthenticatedReleaseStateResultV3:
        if type(capability) is not select_auth._AuthenticatedSpotV7ReleaseSelectionV1:
            raise TypeError("commit_selection requires exact authenticated SELECT capability")
        return self.commit(capability)

    def commit_revocation(
        self,
        capability: revoke_auth._AuthenticatedSpotV7ReleaseRevocationV1,
    ) -> SpotV7AuthenticatedReleaseStateResultV3:
        if type(capability) is not revoke_auth._AuthenticatedSpotV7ReleaseRevocationV1:
            raise TypeError("commit_revocation requires exact authenticated REVOKE capability")
        return self.commit(capability)

    def commit(
        self,
        capability: (
            select_auth._AuthenticatedSpotV7ReleaseSelectionV1
            | revoke_auth._AuthenticatedSpotV7ReleaseRevocationV1
        ),
    ) -> SpotV7AuthenticatedReleaseStateResultV3:
        """Authenticate, replay, and append one exact event or reject as a no-op."""

        try:
            artifacts = _prepare_capability(capability)
            _require_store_identity_matches_artifacts(self._identity, artifacts)
        except TypeError:
            raise
        except ValueError as exc:
            raise SpotV7AuthenticatedReleaseStateStoreErrorV3(
                "AUTHENTICATED_EVENT_INVALID",
                str(exc),
            ) from exc

        connection: sqlite3.Connection | None = None
        commit_started = False
        try:
            connection = self._connect()
            connection.execute("BEGIN IMMEDIATE")
            _validate_schema(connection)
            cursor = _validate_complete_history(connection, self._identity)
            existing = _read_event_by_selector_id(connection, artifacts.selector_input_id)
            if existing is not None:
                result = _resolve_exact_replay(existing, artifacts, cursor, self._identity)
                connection.rollback()
                return result
            try:
                next_cursor = _apply_transition(cursor, artifacts)
            except _TransitionRejectV3 as exc:
                connection.rollback()
                return _result(
                    AuthenticatedReleaseStateDispositionV3.REJECTED,
                    exc.code,
                    artifacts.event_kind,
                    artifacts.selector_input_id,
                    cursor,
                )
            _insert_event(connection, cursor, next_cursor, artifacts, self._identity)
            _cas_meta(connection, cursor, next_cursor)
            commit_started = True
            connection.commit()
            try:
                _fsync_directory(self._path.parent)
            except OSError as exc:
                return self._resolve_post_commit(artifacts, exc)
            return _result(
                AuthenticatedReleaseStateDispositionV3.COMMITTED,
                f"AUTHENTICATED_{artifacts.event_kind.value}_COMMITTED",
                artifacts.event_kind,
                artifacts.selector_input_id,
                next_cursor,
            )
        except SpotV7AuthenticatedReleaseStateStoreErrorV3:
            if connection is not None and connection.in_transaction:
                connection.rollback()
            raise
        except (OSError, sqlite3.Error, TypeError, ValueError) as exc:
            if connection is not None and connection.in_transaction:
                connection.rollback()
            if commit_started:
                return self._resolve_post_commit(artifacts, exc)
            raise SpotV7AuthenticatedReleaseStateStoreErrorV3(
                "STORE_COMMIT_FAILED",
                str(exc),
            ) from exc
        finally:
            if connection is not None:
                connection.close()

    def _resolve_post_commit(
        self,
        artifacts: _AuthenticatedEventArtifactsV3,
        error: BaseException,
    ) -> SpotV7AuthenticatedReleaseStateResultV3:
        connection: sqlite3.Connection | None = None
        try:
            connection = self._connect()
            connection.execute("BEGIN")
            _validate_schema(connection)
            cursor = _validate_complete_history(connection, self._identity)
            row = _read_event_by_selector_id(connection, artifacts.selector_input_id)
            if row is None:
                raise ValueError("committed event is absent during post-commit resolution")
            _resolve_exact_replay(row, artifacts, cursor, self._identity)
            connection.rollback()
            return _result(
                AuthenticatedReleaseStateDispositionV3.COMMITTED,
                f"AUTHENTICATED_{artifacts.event_kind.value}_COMMITTED_POST_COMMIT_RESOLVED",
                artifacts.event_kind,
                artifacts.selector_input_id,
                cursor,
            )
        except (OSError, sqlite3.Error, TypeError, ValueError) as replay_error:
            if connection is not None and connection.in_transaction:
                connection.rollback()
            raise SpotV7AuthenticatedReleaseStateDurabilityUncertainV3(
                selector_input_id=artifacts.selector_input_id,
                detail=f"commit outcome unresolved after {error!r}: {replay_error!r}",
            ) from error
        finally:
            if connection is not None:
                connection.close()

    def _connect(self) -> sqlite3.Connection:
        _validate_database_file(self._path)
        return _connect_database(self._path, self._busy_timeout_ms)


def _prepare_capability(
    capability: object,
) -> _AuthenticatedEventArtifactsV3:
    if (
        isinstance(capability, select_auth._AuthenticatedSpotV7ReleaseSelectionV1)
        and type(capability) is select_auth._AuthenticatedSpotV7ReleaseSelectionV1
    ):
        selected = capability
        if not selected._has_private_seal():
            raise TypeError("store requires sealed authenticated SELECT capability")
        selection_projection = selected._artifacts_for_durable_store_v2()
        selection_artifacts = _revalidate_selection_evidence(
            selection_projection.authentication_evidence_bytes
        )
        _require_selection_projection(selection_projection, selection_artifacts)
        _require_selection_capability(selected, selection_artifacts)
        return selection_artifacts
    if (
        isinstance(capability, revoke_auth._AuthenticatedSpotV7ReleaseRevocationV1)
        and type(capability) is revoke_auth._AuthenticatedSpotV7ReleaseRevocationV1
    ):
        revoked = capability
        if not revoked._has_private_seal():
            raise TypeError("store requires sealed authenticated REVOKE capability")
        revocation_projection = revoked._artifacts_for_durable_store_v1()
        revocation_artifacts = _revalidate_revocation_evidence(
            revocation_projection.authentication_evidence_bytes
        )
        _require_revocation_projection(revocation_projection, revocation_artifacts)
        _require_revocation_capability(revoked, revocation_artifacts)
        return revocation_artifacts
    raise TypeError("store requires exact authenticated SELECT or REVOKE capability")


def _revalidate_selection_evidence(raw: bytes) -> _AuthenticatedEventArtifactsV3:
    retained = select_auth._parse_authentication_evidence_v1(raw)
    authenticated = select_auth.authenticate_spot_v7_release_selection_v1(
        retained.envelope_bytes,
        selector_input_bytes=retained.selector_input_bytes,
        expected_selector_input_id=retained.expected_selector_input_id,
        candidate_bytes=retained.candidate_bytes,
        external_trust_pins=retained.pins,
        trusted_signer_registry=retained.registry,
        signature_envelopes=retained.envelopes,
    )
    if authenticated._evidence_bytes != raw:
        raise ValueError("SELECT authentication evidence does not exactly recompose")
    selector = parse_exact_governed_release_selector_input_v1(
        retained.selector_input_bytes,
        expected_input_id=retained.expected_selector_input_id,
    )
    if selector.operation is not SelectorOperationV1.SELECT:
        raise ValueError("selection evidence does not contain SELECT operation")
    envelope = parse_exact_spot_v7_release_selection_envelope_v1(retained.envelope_bytes)
    candidate = check_exact_spot_v7_release_candidate_manifest_v1(
        retained.candidate_bytes,
        expected_candidate_id=envelope.candidate_id,
    )
    parent, activation, expiration = _candidate_lineage(candidate)
    return _AuthenticatedEventArtifactsV3(
        event_kind=ReleaseStateEventKindV3.SELECT,
        selector=selector,
        candidate=candidate,
        candidate_bytes=retained.candidate_bytes,
        selector_input_bytes=retained.selector_input_bytes,
        envelope_bytes=retained.envelope_bytes,
        record=None,
        record_bytes=None,
        signer_registry_bytes=retained.signer_registry_bytes,
        signature_envelopes_bytes=retained.signature_envelopes_bytes,
        quorum_report_bytes=retained.quorum_report_bytes,
        external_trust_pins_bytes=retained.external_trust_pins_bytes,
        authentication_evidence_bytes=raw,
        parent_candidate_id=parent,
        activation_epoch=activation,
        expiration_epoch=expiration,
        selection_envelope=envelope,
        revocation_envelope=None,
        pins=retained.pins,
    )


def _revalidate_revocation_evidence(raw: bytes) -> _AuthenticatedEventArtifactsV3:
    retained = revoke_auth._parse_authentication_evidence_v1(raw)
    authenticated = revoke_auth.authenticate_spot_v7_release_revocation_v1(
        retained.envelope_bytes,
        revocation_selector_input_bytes=retained.selector_input_bytes,
        expected_revocation_selector_input_id=retained.expected_selector_input_id,
        current_candidate_bytes=retained.candidate_bytes,
        revocation_record_bytes=retained.record_bytes,
        expected_revocation_record_id=retained.pins.expected_revocation_record_id,
        external_trust_pins=retained.pins,
        trusted_signer_registry=retained.registry,
        signature_envelopes=retained.envelopes,
    )
    if authenticated._evidence_bytes != raw:
        raise ValueError("REVOKE authentication evidence does not exactly recompose")
    selector = parse_exact_governed_release_selector_input_v1(
        retained.selector_input_bytes,
        expected_input_id=retained.expected_selector_input_id,
    )
    if selector.operation is not SelectorOperationV1.REVOKE:
        raise ValueError("revocation evidence does not contain REVOKE operation")
    envelope = parse_exact_spot_v7_release_revocation_envelope_v1(retained.envelope_bytes)
    candidate = check_exact_spot_v7_release_candidate_manifest_v1(
        retained.candidate_bytes,
        expected_candidate_id=envelope.current_candidate_id,
    )
    record = parse_exact_spot_v7_revocation_record_v1(
        retained.record_bytes,
        expected_record_id=envelope.revocation_record_id,
    )
    parent, activation, expiration = _candidate_lineage(candidate)
    return _AuthenticatedEventArtifactsV3(
        event_kind=ReleaseStateEventKindV3.REVOKE,
        selector=selector,
        candidate=candidate,
        candidate_bytes=retained.candidate_bytes,
        selector_input_bytes=retained.selector_input_bytes,
        envelope_bytes=retained.envelope_bytes,
        record=record,
        record_bytes=retained.record_bytes,
        signer_registry_bytes=retained.signer_registry_bytes,
        signature_envelopes_bytes=retained.signature_envelopes_bytes,
        quorum_report_bytes=retained.quorum_report_bytes,
        external_trust_pins_bytes=retained.external_trust_pins_bytes,
        authentication_evidence_bytes=raw,
        parent_candidate_id=parent,
        activation_epoch=activation,
        expiration_epoch=expiration,
        selection_envelope=None,
        revocation_envelope=envelope,
        pins=retained.pins,
    )


def _candidate_lineage(
    candidate: SpotV7ReleaseCandidateManifestV1,
) -> tuple[bytes | None, int, int | None]:
    document = cast(dict[str, Any], json.loads(candidate.canonical_bytes))
    lineage = cast(dict[str, Any], document["lineage"])
    return (
        candidate.parent_candidate_id,
        _require_u64(lineage["proposed_activation_epoch"], name="candidate_activation_epoch"),
        _require_optional_u64(
            lineage["proposed_expiration_epoch"],
            name="candidate_expiration_epoch",
        ),
    )


def _require_selection_projection(
    projection: select_auth._AuthenticatedReleaseSelectionDurableArtifactsV2,
    artifacts: _AuthenticatedEventArtifactsV3,
) -> None:
    observed = (
        projection.envelope_bytes,
        projection.selector_input_bytes,
        projection.candidate_bytes,
        projection.signer_registry_bytes,
        projection.signature_envelopes_bytes,
        projection.quorum_report_bytes,
        projection.external_trust_pins_bytes,
        projection.authentication_evidence_bytes,
    )
    if observed != _projection_values(artifacts):
        raise ValueError("SELECT durable projection differs from revalidated evidence")


def _require_revocation_projection(
    projection: revoke_auth._AuthenticatedReleaseRevocationDurableArtifactsV1,
    artifacts: _AuthenticatedEventArtifactsV3,
) -> None:
    observed = (
        projection.envelope_bytes,
        projection.revocation_selector_input_bytes,
        projection.current_candidate_bytes,
        projection.signer_registry_bytes,
        projection.signature_envelopes_bytes,
        projection.quorum_report_bytes,
        projection.external_trust_pins_bytes,
        projection.authentication_evidence_bytes,
        projection.revocation_record_bytes,
    )
    expected = (*_projection_values(artifacts), artifacts.record_bytes)
    if observed != expected:
        raise ValueError("REVOKE durable projection differs from revalidated evidence")


def _projection_values(artifacts: _AuthenticatedEventArtifactsV3) -> tuple[bytes, ...]:
    return (
        artifacts.envelope_bytes,
        artifacts.selector_input_bytes,
        artifacts.candidate_bytes,
        artifacts.signer_registry_bytes,
        artifacts.signature_envelopes_bytes,
        artifacts.quorum_report_bytes,
        artifacts.external_trust_pins_bytes,
        artifacts.authentication_evidence_bytes,
    )


def _require_selection_capability(
    capability: select_auth._AuthenticatedSpotV7ReleaseSelectionV1,
    artifacts: _AuthenticatedEventArtifactsV3,
) -> None:
    envelope = _require_selection_envelope(artifacts)
    observed = (
        capability.selector_input_id,
        capability.selected_candidate_id,
        capability.selected_candidate_sha256,
        capability.release_revision,
        capability.evaluation_epoch,
        capability.chain_id,
        capability.domain_id,
        capability.signer_registry_hash,
        capability.signer_registry_revision,
        capability.quorum_threshold,
        capability.evidence_sha256,
    )
    expected = (
        artifacts.selector_input_id,
        artifacts.candidate.candidate_id,
        artifacts.candidate_sha256,
        artifacts.release_revision,
        artifacts.evaluation_epoch,
        envelope.chain_id,
        envelope.domain_id,
        envelope.signer_registry_hash,
        envelope.signer_registry_revision,
        envelope.quorum_threshold,
        artifacts.authentication_evidence_sha256.hex(),
    )
    if observed != expected:
        raise ValueError("authenticated SELECT capability differs from exact evidence")


def _require_revocation_capability(
    capability: revoke_auth._AuthenticatedSpotV7ReleaseRevocationV1,
    artifacts: _AuthenticatedEventArtifactsV3,
) -> None:
    envelope = _require_revocation_envelope(artifacts)
    record = _require_revocation_record(artifacts)
    observed = (
        capability.revocation_selector_input_id,
        capability.current_candidate_id,
        capability.current_candidate_sha256,
        capability.current_release_revision,
        capability.current_select_input_id,
        capability.revocation_record_id,
        capability.revocation_effective_epoch,
        capability.revocation_record_revision,
        capability.revocation_reason_code,
        capability.revocation_issuer_set_root,
        capability.evaluation_epoch,
        capability.chain_id,
        capability.domain_id,
        capability.signer_registry_hash,
        capability.signer_registry_revision,
        capability.quorum_threshold,
        capability.evidence_sha256,
    )
    expected = (
        artifacts.selector_input_id,
        artifacts.candidate.candidate_id,
        artifacts.candidate_sha256,
        artifacts.release_revision,
        envelope.current_select_input_id,
        record.record_id,
        record.effective_epoch,
        record.record_revision,
        record.reason_code,
        record.issuer_set_root,
        artifacts.evaluation_epoch,
        envelope.chain_id,
        envelope.domain_id,
        envelope.signer_registry_hash,
        envelope.signer_registry_revision,
        envelope.quorum_threshold,
        artifacts.authentication_evidence_sha256.hex(),
    )
    if observed != expected:
        raise ValueError("authenticated REVOKE capability differs from exact evidence")


def derive_selection_static_trust_pin_identity_v3(
    pins: select_auth.SpotV7ReleaseSelectionExternalTrustPinsV1,
) -> bytes:
    """Derive configured static SELECT-pin identity; no governance is implied."""

    return _domain_hash(
        SPOT_V7_SELECTION_DERIVED_STATIC_TRUST_PIN_DOMAIN_V3.encode("ascii"),
        canonical_json_bytes(
            {
                "application_id": pins.application_id,
                "chain_id": pins.chain_id,
                "domain_id": pins.domain_id,
                "expected_quorum_threshold": pins.expected_quorum_threshold,
                "expected_signer_registry_hash": pins.expected_signer_registry_hash,
                "payload_kind": SPOT_V7_RELEASE_SELECTION_PAYLOAD_KIND_V1,
                "release_profile": pins.release_profile,
                "revocation_policy_root": _root_text(pins.revocation_policy_root),
                "revocation_registry_root": _root_text(pins.revocation_registry_root),
                "rollback_policy_root": _root_text(pins.rollback_policy_root),
                "signer_registry_activation_epoch": pins.signer_registry_activation_epoch,
                "signer_registry_id": pins.signer_registry_id,
                "signer_registry_revision": pins.signer_registry_revision,
                "signer_registry_revocation_epoch": pins.signer_registry_revocation_epoch,
            }
        ),
    )


def derive_revocation_static_trust_pin_identity_v3(
    pins: revoke_auth.SpotV7ReleaseRevocationExternalTrustPinsV1,
) -> bytes:
    """Derive configured static REVOKE-pin identity; no governance is implied."""

    return _domain_hash(
        SPOT_V7_REVOCATION_DERIVED_STATIC_TRUST_PIN_DOMAIN_V3.encode("ascii"),
        canonical_json_bytes(
            {
                "application_id": pins.application_id,
                "chain_id": pins.chain_id,
                "domain_id": pins.domain_id,
                "expected_quorum_threshold": pins.expected_quorum_threshold,
                "expected_signer_registry_hash": pins.expected_signer_registry_hash,
                "payload_kind": SPOT_V7_RELEASE_REVOCATION_PAYLOAD_KIND_V1,
                "release_profile": pins.release_profile,
                "revocation_policy_root": _root_text(pins.revocation_policy_root),
                "revocation_registry_root": _root_text(pins.revocation_registry_root),
                "rollback_policy_root": _root_text(pins.rollback_policy_root),
                "signer_registry_activation_epoch": pins.signer_registry_activation_epoch,
                "signer_registry_id": pins.signer_registry_id,
                "signer_registry_revision": pins.signer_registry_revision,
                "signer_registry_revocation_epoch": pins.signer_registry_revocation_epoch,
            }
        ),
    )


def _require_store_identity_matches_artifacts(
    identity: SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    artifacts: _AuthenticatedEventArtifactsV3,
) -> None:
    if artifacts.event_kind is ReleaseStateEventKindV3.SELECT:
        selection_envelope = _require_selection_envelope(artifacts)
        selection_pins = cast(
            select_auth.SpotV7ReleaseSelectionExternalTrustPinsV1,
            artifacts.pins,
        )
        checks = (
            (
                selection_envelope.application_id == identity.application_id,
                "APPLICATION_ID_MISMATCH",
            ),
            (selection_envelope.chain_id == identity.chain_id, "CHAIN_ID_MISMATCH"),
            (selection_envelope.domain_id == identity.domain_id, "DOMAIN_ID_MISMATCH"),
            (
                selection_envelope.release_profile == identity.release_profile,
                "RELEASE_PROFILE_MISMATCH",
            ),
            (
                selection_envelope.signer_registry_id == identity.selection_signer_registry_id,
                "SELECTION_REGISTRY_ID_MISMATCH",
            ),
            (
                selection_envelope.signer_registry_hash == identity.selection_signer_registry_hash,
                "SELECTION_REGISTRY_HASH_MISMATCH",
            ),
            (
                selection_envelope.signer_registry_revision
                == identity.selection_signer_registry_revision,
                "SELECTION_REGISTRY_REVISION_MISMATCH",
            ),
            (
                selection_envelope.signer_registry_activation_epoch
                == identity.selection_signer_registry_activation_epoch,
                "SELECTION_REGISTRY_ACTIVATION_MISMATCH",
            ),
            (
                selection_envelope.signer_registry_revocation_epoch
                == identity.selection_signer_registry_revocation_epoch,
                "SELECTION_REGISTRY_REVOCATION_MISMATCH",
            ),
            (
                selection_envelope.quorum_threshold == identity.selection_quorum_threshold,
                "SELECTION_QUORUM_MISMATCH",
            ),
            (
                derive_selection_static_trust_pin_identity_v3(selection_pins)
                == identity.selection_derived_static_trust_pin_identity,
                "SELECTION_TRUST_PIN_IDENTITY_MISMATCH",
            ),
            (
                selection_envelope.rollback_policy_root == identity.rollback_policy_root,
                "ROLLBACK_POLICY_MISMATCH",
            ),
            (
                selection_envelope.revocation_policy_root == identity.revocation_policy_root,
                "REVOCATION_POLICY_MISMATCH",
            ),
            (
                selection_envelope.revocation_registry_root == identity.revocation_registry_root,
                "REVOCATION_REGISTRY_MISMATCH",
            ),
        )
    else:
        revocation_envelope = _require_revocation_envelope(artifacts)
        revocation_pins = cast(
            revoke_auth.SpotV7ReleaseRevocationExternalTrustPinsV1,
            artifacts.pins,
        )
        checks = (
            (
                revocation_envelope.application_id == identity.application_id,
                "APPLICATION_ID_MISMATCH",
            ),
            (revocation_envelope.chain_id == identity.chain_id, "CHAIN_ID_MISMATCH"),
            (revocation_envelope.domain_id == identity.domain_id, "DOMAIN_ID_MISMATCH"),
            (
                revocation_envelope.release_profile == identity.release_profile,
                "RELEASE_PROFILE_MISMATCH",
            ),
            (
                revocation_envelope.signer_registry_id == identity.revocation_signer_registry_id,
                "REVOCATION_REGISTRY_ID_MISMATCH",
            ),
            (
                revocation_envelope.signer_registry_hash
                == identity.revocation_signer_registry_hash,
                "REVOCATION_REGISTRY_HASH_MISMATCH",
            ),
            (
                revocation_envelope.signer_registry_revision
                == identity.revocation_signer_registry_revision,
                "REVOCATION_REGISTRY_REVISION_MISMATCH",
            ),
            (
                revocation_envelope.signer_registry_activation_epoch
                == identity.revocation_signer_registry_activation_epoch,
                "REVOCATION_REGISTRY_ACTIVATION_MISMATCH",
            ),
            (
                revocation_envelope.signer_registry_revocation_epoch
                == identity.revocation_signer_registry_revocation_epoch,
                "REVOCATION_REGISTRY_REVOCATION_MISMATCH",
            ),
            (
                revocation_envelope.quorum_threshold == identity.revocation_quorum_threshold,
                "REVOCATION_QUORUM_MISMATCH",
            ),
            (
                derive_revocation_static_trust_pin_identity_v3(revocation_pins)
                == identity.revocation_derived_static_trust_pin_identity,
                "REVOCATION_TRUST_PIN_IDENTITY_MISMATCH",
            ),
            (
                revocation_envelope.rollback_policy_root == identity.rollback_policy_root,
                "ROLLBACK_POLICY_MISMATCH",
            ),
            (
                revocation_envelope.revocation_policy_root == identity.revocation_policy_root,
                "REVOCATION_POLICY_MISMATCH",
            ),
            (
                revocation_envelope.revocation_registry_root == identity.revocation_registry_root,
                "REVOCATION_REGISTRY_MISMATCH",
            ),
        )
    for accepted, code in checks:
        if not accepted:
            raise _TransitionRejectV3(code)


def _apply_transition(
    cursor: SpotV7AuthenticatedReleaseStateCursorV3,
    artifacts: _AuthenticatedEventArtifactsV3,
) -> SpotV7AuthenticatedReleaseStateCursorV3:
    if artifacts.event_kind is ReleaseStateEventKindV3.SELECT:
        return _apply_select(cursor, artifacts)
    return _apply_revoke(cursor, artifacts)


def _apply_select(
    cursor: SpotV7AuthenticatedReleaseStateCursorV3,
    artifacts: _AuthenticatedEventArtifactsV3,
) -> SpotV7AuthenticatedReleaseStateCursorV3:
    selector = artifacts.selector
    envelope = _require_selection_envelope(artifacts)
    if cursor.current_revoked:
        raise _TransitionRejectV3("CURRENT_RELEASE_TERMINALLY_REVOKED")
    _require_epoch_and_cas(cursor, artifacts)
    if selector.evaluation_epoch < artifacts.activation_epoch:
        raise _TransitionRejectV3("CANDIDATE_NOT_ACTIVE")
    if (
        artifacts.expiration_epoch is not None
        and selector.evaluation_epoch >= artifacts.expiration_epoch
    ):
        raise _TransitionRejectV3("CANDIDATE_EXPIRED")
    if envelope.expected_database_revision != selector.expected_database_revision:
        raise _TransitionRejectV3("ENVELOPE_DATABASE_REVISION_MISMATCH")
    if envelope.expected_current_candidate_id != selector.expected_current_candidate_id:
        raise _TransitionRejectV3("ENVELOPE_CURRENT_CANDIDATE_MISMATCH")
    if envelope.expected_current_select_input_id != selector.expected_current_select_input_id:
        raise _TransitionRejectV3("ENVELOPE_CURRENT_SELECTION_MISMATCH")
    current_revision = cursor.current_release_revision
    if current_revision is None:
        if artifacts.release_revision != 1 or artifacts.parent_candidate_id is not None:
            raise _TransitionRejectV3("GENESIS_LINEAGE_MISMATCH")
    else:
        if artifacts.release_revision < current_revision:
            raise _TransitionRejectV3("RELEASE_ROLLBACK_REJECTED")
        if artifacts.release_revision == current_revision:
            code = (
                "RELEASE_REPLAY_CONFLICT"
                if artifacts.candidate.candidate_id == cursor.current_candidate_id
                else "RELEASE_FORK_REJECTED"
            )
            raise _TransitionRejectV3(code)
        if artifacts.release_revision != current_revision + 1:
            raise _TransitionRejectV3("RELEASE_REVISION_GAP")
        if artifacts.parent_candidate_id != cursor.current_candidate_id:
            raise _TransitionRejectV3("RELEASE_FORK_REJECTED")
    return _next_cursor(
        cursor,
        artifacts,
        current_revoked=False,
        current_revocation_record_id=None,
    )


def _apply_revoke(
    cursor: SpotV7AuthenticatedReleaseStateCursorV3,
    artifacts: _AuthenticatedEventArtifactsV3,
) -> SpotV7AuthenticatedReleaseStateCursorV3:
    if cursor.current_candidate_id is None:
        raise _TransitionRejectV3("REVOCATION_WITHOUT_CURRENT_HEAD")
    if cursor.current_revoked:
        raise _TransitionRejectV3("CURRENT_RELEASE_ALREADY_REVOKED")
    _require_epoch_and_cas(cursor, artifacts)
    envelope = _require_revocation_envelope(artifacts)
    record = _require_revocation_record(artifacts)
    if artifacts.candidate.candidate_id != cursor.current_candidate_id:
        raise _TransitionRejectV3("NONCURRENT_CANDIDATE_REVOCATION")
    if artifacts.candidate_sha256 != cursor.current_candidate_sha256:
        raise _TransitionRejectV3("CURRENT_CANDIDATE_SHA256_MISMATCH")
    if artifacts.release_revision != cursor.current_release_revision:
        raise _TransitionRejectV3("CURRENT_RELEASE_REVISION_MISMATCH")
    if envelope.current_candidate_id != cursor.current_candidate_id:
        raise _TransitionRejectV3("ENVELOPE_CURRENT_CANDIDATE_MISMATCH")
    if envelope.current_candidate_sha256 != cursor.current_candidate_sha256:
        raise _TransitionRejectV3("ENVELOPE_CURRENT_CANDIDATE_SHA256_MISMATCH")
    if envelope.current_release_revision != cursor.current_release_revision:
        raise _TransitionRejectV3("ENVELOPE_CURRENT_RELEASE_REVISION_MISMATCH")
    if envelope.current_select_input_id != cursor.current_select_input_id:
        raise _TransitionRejectV3("ENVELOPE_CURRENT_SELECTION_MISMATCH")
    if envelope.last_evaluation_epoch != cursor.last_evaluation_epoch:
        raise _TransitionRejectV3("ENVELOPE_LAST_EVALUATION_EPOCH_MISMATCH")
    if record.effective_epoch > artifacts.evaluation_epoch:
        raise _TransitionRejectV3("REVOCATION_EFFECTIVE_EPOCH_FUTURE")
    return _next_cursor(
        cursor,
        artifacts,
        current_revoked=True,
        current_revocation_record_id=record.record_id,
    )


def _require_epoch_and_cas(
    cursor: SpotV7AuthenticatedReleaseStateCursorV3,
    artifacts: _AuthenticatedEventArtifactsV3,
) -> None:
    selector = artifacts.selector
    if (
        cursor.last_evaluation_epoch is not None
        and selector.evaluation_epoch < cursor.last_evaluation_epoch
    ):
        raise _TransitionRejectV3("EVALUATION_EPOCH_ROLLBACK_REJECTED")
    if selector.expected_database_revision != cursor.database_revision:
        raise _TransitionRejectV3("DATABASE_REVISION_CAS_MISMATCH")
    if selector.expected_current_candidate_id != cursor.current_candidate_id:
        raise _TransitionRejectV3("CURRENT_CANDIDATE_CAS_MISMATCH")
    if selector.expected_current_select_input_id != cursor.current_select_input_id:
        raise _TransitionRejectV3("CURRENT_SELECTION_CAS_MISMATCH")


def _next_cursor(
    cursor: SpotV7AuthenticatedReleaseStateCursorV3,
    artifacts: _AuthenticatedEventArtifactsV3,
    *,
    current_revoked: bool,
    current_revocation_record_id: bytes | None,
) -> SpotV7AuthenticatedReleaseStateCursorV3:
    next_revision = cursor.database_revision + 1
    if next_revision > MAX_AUTHENTICATED_RELEASE_EVENTS_V3:
        raise _TransitionRejectV3("EVENT_LIMIT_REACHED")
    if artifacts.event_kind is ReleaseStateEventKindV3.REVOKE:
        candidate_id = cursor.current_candidate_id
        candidate_sha256 = cursor.current_candidate_sha256
        release_revision = cursor.current_release_revision
        select_input_id = cursor.current_select_input_id
    else:
        candidate_id = artifacts.candidate.candidate_id
        candidate_sha256 = artifacts.candidate_sha256
        release_revision = artifacts.release_revision
        select_input_id = artifacts.selector_input_id
    return SpotV7AuthenticatedReleaseStateCursorV3(
        database_revision=next_revision,
        state_root=_event_state_root(cursor.state_root, next_revision, artifacts),
        last_evaluation_epoch=artifacts.evaluation_epoch,
        current_candidate_id=candidate_id,
        current_candidate_sha256=candidate_sha256,
        current_release_revision=release_revision,
        current_select_input_id=select_input_id,
        current_revoked=current_revoked,
        current_revocation_record_id=current_revocation_record_id,
    )


def _insert_event(
    connection: sqlite3.Connection,
    previous: SpotV7AuthenticatedReleaseStateCursorV3,
    result: SpotV7AuthenticatedReleaseStateCursorV3,
    artifacts: _AuthenticatedEventArtifactsV3,
    identity: SpotV7AuthenticatedReleaseStateStoreIdentityV3,
) -> None:
    kind = artifacts.event_kind
    is_select = kind is ReleaseStateEventKindV3.SELECT
    connection.execute(
        """
        INSERT INTO spot_v7_authenticated_release_state_events_v3 (
            event_revision_be, event_kind, selector_input_id, selector_input_bytes,
            candidate_id, candidate_sha256, candidate_bytes, release_revision_be,
            evaluation_epoch_be, envelope_bytes, revocation_record_bytes,
            revocation_record_id, signer_registry_bytes, signature_envelopes_bytes,
            quorum_report_bytes, external_trust_pins_bytes,
            derived_static_trust_pin_identity, authentication_evidence_bytes,
            authentication_evidence_sha256, select_candidate_id,
            select_release_revision_be, revoke_candidate_id,
            revoke_release_revision_be, previous_state_root, result_state_root,
            durable_authenticated_release_state_recorded,
            release_governed_trust_roots_authenticated,
            external_monotonic_state_anchor_verified,
            hostile_same_interpreter_resistance_established,
            same_uid_path_substitution_resistance_established,
            revocation_authority, release_authority, runtime_authority,
            settlement_authority, production_authority
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0)
        """,
        (
            _u64be(result.database_revision),
            kind.value,
            artifacts.selector_input_id,
            artifacts.selector_input_bytes,
            artifacts.candidate.candidate_id,
            artifacts.candidate_sha256,
            artifacts.candidate_bytes,
            _u64be(artifacts.release_revision),
            _u64be(artifacts.evaluation_epoch),
            artifacts.envelope_bytes,
            artifacts.record_bytes,
            artifacts.revocation_record_id,
            artifacts.signer_registry_bytes,
            artifacts.signature_envelopes_bytes,
            artifacts.quorum_report_bytes,
            artifacts.external_trust_pins_bytes,
            _event_derived_static_trust_pin_identity(identity, kind),
            artifacts.authentication_evidence_bytes,
            artifacts.authentication_evidence_sha256,
            artifacts.candidate.candidate_id if is_select else None,
            _u64be(artifacts.release_revision) if is_select else None,
            None if is_select else artifacts.candidate.candidate_id,
            None if is_select else _u64be(artifacts.release_revision),
            previous.state_root,
            result.state_root,
        ),
    )


def _cas_meta(
    connection: sqlite3.Connection,
    previous: SpotV7AuthenticatedReleaseStateCursorV3,
    result: SpotV7AuthenticatedReleaseStateCursorV3,
) -> None:
    updated = connection.execute(
        """
        UPDATE spot_v7_authenticated_release_state_meta_v3
        SET database_revision_be = ?, state_root = ?, event_count = ?,
            last_evaluation_epoch_be = ?, current_candidate_id = ?,
            current_candidate_sha256 = ?, current_release_revision_be = ?,
            current_select_input_id = ?, current_revoked = ?,
            current_revocation_record_id = ?
        WHERE singleton = 1 AND database_revision_be = ? AND state_root = ?
        """,
        (
            _u64be(result.database_revision),
            result.state_root,
            result.database_revision,
            _optional_u64be(result.last_evaluation_epoch),
            result.current_candidate_id,
            result.current_candidate_sha256,
            _optional_u64be(result.current_release_revision),
            result.current_select_input_id,
            int(result.current_revoked),
            result.current_revocation_record_id,
            _u64be(previous.database_revision),
            previous.state_root,
        ),
    )
    if updated.rowcount != 1:
        raise ValueError("authenticated release-state metadata CAS failed")


def _resolve_exact_replay(
    row: sqlite3.Row,
    artifacts: _AuthenticatedEventArtifactsV3,
    cursor: SpotV7AuthenticatedReleaseStateCursorV3,
    identity: SpotV7AuthenticatedReleaseStateStoreIdentityV3,
) -> SpotV7AuthenticatedReleaseStateResultV3:
    if _event_storage_values(row) != _artifact_storage_values(artifacts, identity):
        raise ValueError("stored selector identity collision or authenticated evidence drift")
    return _result(
        AuthenticatedReleaseStateDispositionV3.IDEMPOTENT,
        f"EXACT_AUTHENTICATED_{artifacts.event_kind.value}_REPLAY",
        artifacts.event_kind,
        artifacts.selector_input_id,
        cursor,
    )


def _validate_complete_history(
    connection: sqlite3.Connection,
    identity: SpotV7AuthenticatedReleaseStateStoreIdentityV3,
) -> SpotV7AuthenticatedReleaseStateCursorV3:
    return _validate_complete_history_chain(connection, identity)[-1]


def _validate_complete_history_chain(
    connection: sqlite3.Connection,
    identity: SpotV7AuthenticatedReleaseStateStoreIdentityV3,
) -> tuple[SpotV7AuthenticatedReleaseStateCursorV3, ...]:
    _validate_database_integrity(connection)
    meta = _read_meta(connection)
    _validate_meta_identity(meta, identity)
    cursor = _genesis_cursor(identity)
    cursors = [cursor]
    rows = _read_all_events(connection)
    if len(rows) > MAX_AUTHENTICATED_RELEASE_EVENTS_V3:
        raise ValueError("authenticated release event count exceeds maximum")
    for revision, row in enumerate(rows, start=1):
        if bytes(row["event_revision_be"]) != _u64be(revision):
            raise ValueError("authenticated release-state revisions are not contiguous")
        try:
            kind = ReleaseStateEventKindV3(str(row["event_kind"]))
        except ValueError as exc:
            raise ValueError("stored event kind is invalid") from exc
        evidence = bytes(row["authentication_evidence_bytes"])
        artifacts = (
            _revalidate_selection_evidence(evidence)
            if kind is ReleaseStateEventKindV3.SELECT
            else _revalidate_revocation_evidence(evidence)
        )
        if artifacts.event_kind is not kind:
            raise ValueError("stored event kind differs from authenticated evidence")
        _require_store_identity_matches_artifacts(identity, artifacts)
        if _event_storage_values(row) != _artifact_storage_values(artifacts, identity):
            raise ValueError("stored authenticated event projection mismatch")
        if bytes(row["previous_state_root"]) != cursor.state_root:
            raise ValueError("stored authenticated event previous root mismatch")
        cursor = _apply_transition(cursor, artifacts)
        if cursor.database_revision != revision:
            raise ValueError("replayed authenticated event revision mismatch")
        if bytes(row["result_state_root"]) != cursor.state_root:
            raise ValueError("stored authenticated event result root mismatch")
        cursors.append(cursor)
        expected_flags = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)
        observed_flags = (
            int(row["durable_authenticated_release_state_recorded"]),
            int(row["release_governed_trust_roots_authenticated"]),
            int(row["external_monotonic_state_anchor_verified"]),
            int(row["hostile_same_interpreter_resistance_established"]),
            int(row["same_uid_path_substitution_resistance_established"]),
            int(row["revocation_authority"]),
            int(row["release_authority"]),
            int(row["runtime_authority"]),
            int(row["settlement_authority"]),
            int(row["production_authority"]),
        )
        if observed_flags != expected_flags:
            raise ValueError("stored authenticated release-state authority flags mismatch")
    if int(meta["event_count"]) != len(rows):
        raise ValueError("authenticated release-state event count mismatch")
    if _cursor_storage_values(cursor) != _meta_cursor_values(meta):
        raise ValueError("metadata disagrees with replayed release-state history")
    return tuple(cursors)


def _event_storage_values(row: sqlite3.Row) -> tuple[object, ...]:
    nullable = ("revocation_record_bytes", "revocation_record_id")
    return (
        str(row["event_kind"]),
        bytes(row["selector_input_id"]),
        bytes(row["selector_input_bytes"]),
        bytes(row["candidate_id"]),
        bytes(row["candidate_sha256"]),
        bytes(row["candidate_bytes"]),
        bytes(row["release_revision_be"]),
        bytes(row["evaluation_epoch_be"]),
        bytes(row["envelope_bytes"]),
        *(_optional_blob(row[name]) for name in nullable),
        bytes(row["signer_registry_bytes"]),
        bytes(row["signature_envelopes_bytes"]),
        bytes(row["quorum_report_bytes"]),
        bytes(row["external_trust_pins_bytes"]),
        bytes(row["derived_static_trust_pin_identity"]),
        bytes(row["authentication_evidence_bytes"]),
        bytes(row["authentication_evidence_sha256"]),
        _optional_blob(row["select_candidate_id"]),
        _optional_blob(row["select_release_revision_be"]),
        _optional_blob(row["revoke_candidate_id"]),
        _optional_blob(row["revoke_release_revision_be"]),
    )


def _artifact_storage_values(
    artifacts: _AuthenticatedEventArtifactsV3,
    identity: SpotV7AuthenticatedReleaseStateStoreIdentityV3,
) -> tuple[object, ...]:
    is_select = artifacts.event_kind is ReleaseStateEventKindV3.SELECT
    return (
        artifacts.event_kind.value,
        artifacts.selector_input_id,
        artifacts.selector_input_bytes,
        artifacts.candidate.candidate_id,
        artifacts.candidate_sha256,
        artifacts.candidate_bytes,
        _u64be(artifacts.release_revision),
        _u64be(artifacts.evaluation_epoch),
        artifacts.envelope_bytes,
        artifacts.record_bytes,
        artifacts.revocation_record_id,
        artifacts.signer_registry_bytes,
        artifacts.signature_envelopes_bytes,
        artifacts.quorum_report_bytes,
        artifacts.external_trust_pins_bytes,
        _event_derived_static_trust_pin_identity(identity, artifacts.event_kind),
        artifacts.authentication_evidence_bytes,
        artifacts.authentication_evidence_sha256,
        artifacts.candidate.candidate_id if is_select else None,
        _u64be(artifacts.release_revision) if is_select else None,
        None if is_select else artifacts.candidate.candidate_id,
        None if is_select else _u64be(artifacts.release_revision),
    )


def _event_derived_static_trust_pin_identity(
    identity: SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    kind: ReleaseStateEventKindV3,
) -> bytes:
    if kind is ReleaseStateEventKindV3.SELECT:
        return identity.selection_derived_static_trust_pin_identity
    return identity.revocation_derived_static_trust_pin_identity


def _initialize_or_validate(
    connection: sqlite3.Connection,
    identity: SpotV7AuthenticatedReleaseStateStoreIdentityV3,
) -> None:
    if not connection.in_transaction:
        raise ValueError("release-state initialization requires a transaction")
    existing = connection.execute(
        "SELECT name FROM sqlite_master WHERE name NOT LIKE 'sqlite_%'"
    ).fetchall()
    if not existing:
        if int(connection.execute("PRAGMA application_id").fetchone()[0]) != 0:
            raise ValueError("empty release-state database has an application_id")
        if int(connection.execute("PRAGMA user_version").fetchone()[0]) != 0:
            raise ValueError("empty release-state database has a user_version")
        connection.execute(f"PRAGMA application_id = {STORE_APPLICATION_ID_V3}")
        connection.execute(f"PRAGMA user_version = {STORE_SCHEMA_VERSION_V3}")
        for statement in _SCHEMA_STATEMENTS_V3:
            connection.execute(statement)
        genesis = _genesis_cursor(identity)
        connection.execute(
            """
            INSERT INTO spot_v7_authenticated_release_state_meta_v3 (
                singleton, schema_version, store_identity_bytes,
                store_identity_sha256, database_revision_be, state_root,
                event_count, last_evaluation_epoch_be, current_candidate_id,
                current_candidate_sha256, current_release_revision_be,
                current_select_input_id, current_revoked,
                current_revocation_record_id,
                release_governed_trust_roots_authenticated,
                external_monotonic_state_anchor_verified,
                hostile_same_interpreter_resistance_established,
                same_uid_path_substitution_resistance_established,
                revocation_authority, release_authority, runtime_authority,
                settlement_authority, production_authority
            ) VALUES (1, 3, ?, ?, ?, ?, 0, NULL, NULL, NULL, NULL, NULL, 0, NULL, 0, 0, 0, 0, 0, 0, 0, 0, 0)
            """,
            (
                identity.canonical_bytes,
                identity.identity_sha256,
                _u64be(0),
                genesis.state_root,
            ),
        )
    _validate_schema(connection)
    _validate_complete_history(connection, identity)


def _validate_schema(connection: sqlite3.Connection) -> None:
    if int(connection.execute("PRAGMA application_id").fetchone()[0]) != STORE_APPLICATION_ID_V3:
        raise ValueError("authenticated release-state application_id mismatch")
    if int(connection.execute("PRAGMA user_version").fetchone()[0]) != STORE_SCHEMA_VERSION_V3:
        raise ValueError("authenticated release-state user_version mismatch")
    rows = connection.execute(
        """
        SELECT type, name, sql FROM sqlite_master
        WHERE name NOT LIKE 'sqlite_%'
        ORDER BY type, name
        """
    ).fetchall()
    observed = {(str(row["type"]), str(row["name"])) for row in rows}
    expected = {("table", name) for name in _EXPECTED_SCHEMA_SQL_V3}
    if observed != expected:
        raise ValueError("authenticated release-state schema object set mismatch")
    for row in rows:
        name = str(row["name"])
        if _normalize_sql(str(row["sql"])) != _normalize_sql(_EXPECTED_SCHEMA_SQL_V3[name]):
            raise ValueError(f"authenticated release-state schema SQL mismatch for {name}")


def _validate_meta_identity(
    row: sqlite3.Row,
    identity: SpotV7AuthenticatedReleaseStateStoreIdentityV3,
) -> None:
    observed = (
        int(row["schema_version"]),
        bytes(row["store_identity_bytes"]),
        bytes(row["store_identity_sha256"]),
        int(row["release_governed_trust_roots_authenticated"]),
        int(row["external_monotonic_state_anchor_verified"]),
        int(row["hostile_same_interpreter_resistance_established"]),
        int(row["same_uid_path_substitution_resistance_established"]),
        int(row["revocation_authority"]),
        int(row["release_authority"]),
        int(row["runtime_authority"]),
        int(row["settlement_authority"]),
        int(row["production_authority"]),
    )
    expected = (3, identity.canonical_bytes, identity.identity_sha256, 0, 0, 0, 0, 0, 0, 0, 0, 0)
    if observed != expected:
        raise ValueError("authenticated release-state store identity drift")


def _validate_database_integrity(connection: sqlite3.Connection) -> None:
    quick = connection.execute("PRAGMA quick_check").fetchall()
    if len(quick) != 1 or quick[0][0] != "ok":
        raise ValueError("authenticated release-state quick_check failed")
    if connection.execute("PRAGMA foreign_key_check").fetchone() is not None:
        raise ValueError("authenticated release-state foreign_key_check failed")


def _read_meta(connection: sqlite3.Connection) -> sqlite3.Row:
    row = connection.execute(
        "SELECT * FROM spot_v7_authenticated_release_state_meta_v3 WHERE singleton = 1"
    ).fetchone()
    if row is None:
        raise ValueError("authenticated release-state metadata row missing")
    return row


def _read_all_events(connection: sqlite3.Connection) -> list[sqlite3.Row]:
    return connection.execute(
        "SELECT * FROM spot_v7_authenticated_release_state_events_v3 ORDER BY event_revision_be"
    ).fetchall()


def _read_event_by_selector_id(
    connection: sqlite3.Connection,
    selector_input_id: bytes,
) -> sqlite3.Row | None:
    return connection.execute(
        "SELECT * FROM spot_v7_authenticated_release_state_events_v3 WHERE selector_input_id = ?",
        (selector_input_id,),
    ).fetchone()


def _build_current_release_snapshot(
    connection: sqlite3.Connection,
    identity: SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    cursor: SpotV7AuthenticatedReleaseStateCursorV3,
) -> _AuthorityNeutralCurrentReleaseSnapshotV1:
    if not connection.in_transaction:
        raise ValueError("current-release snapshot requires a transaction")
    if cursor.database_revision == 0:
        raise ValueError("current release is empty")
    if cursor.current_revoked:
        raise ValueError("current release is revoked")
    candidate_id = cursor.current_candidate_id
    candidate_sha256 = cursor.current_candidate_sha256
    release_revision = cursor.current_release_revision
    select_input_id = cursor.current_select_input_id
    evaluation_epoch = cursor.last_evaluation_epoch
    if (
        candidate_id is None
        or candidate_sha256 is None
        or release_revision is None
        or select_input_id is None
        or evaluation_epoch is None
    ):
        raise ValueError("current release cursor is incomplete")
    row = _read_event_by_selector_id(connection, select_input_id)
    if row is None or str(row["event_kind"]) != ReleaseStateEventKindV3.SELECT.value:
        raise ValueError("current SELECT event is absent")
    candidate_bytes = bytes(row["candidate_bytes"])
    candidate = check_exact_spot_v7_release_candidate_manifest_v1(
        candidate_bytes,
        expected_candidate_id=candidate_id,
    )
    observed = (
        bytes(row["candidate_id"]),
        hashlib.sha256(candidate_bytes).digest(),
        bytes(row["candidate_sha256"]),
        bytes(row["release_revision_be"]),
        bytes(row["selector_input_id"]),
        candidate.release_revision,
    )
    expected = (
        candidate_id,
        candidate_sha256,
        candidate_sha256,
        _u64be(release_revision),
        select_input_id,
        release_revision,
    )
    if observed != expected:
        raise ValueError("current release projection differs from authenticated cursor")
    return _AuthorityNeutralCurrentReleaseSnapshotV1._from_verified(
        store_identity_sha256=identity.identity_sha256,
        database_revision=cursor.database_revision,
        last_evaluation_epoch=evaluation_epoch,
        state_root=cursor.state_root,
        current_candidate_id=candidate_id,
        current_candidate_sha256=candidate_sha256,
        current_release_revision=release_revision,
        current_select_input_id=select_input_id,
        current_revocation_record_id=None,
        current_candidate_bytes=candidate_bytes,
        seal=_CURRENT_RELEASE_SNAPSHOT_SEAL_V1,
    )


def _genesis_cursor(
    identity: SpotV7AuthenticatedReleaseStateStoreIdentityV3,
) -> SpotV7AuthenticatedReleaseStateCursorV3:
    return SpotV7AuthenticatedReleaseStateCursorV3(
        database_revision=0,
        state_root=_domain_hash(
            _GENESIS_STATE_DOMAIN_V3,
            STORE_SCHEMA_VERSION_V3.to_bytes(4, "big") + identity.identity_sha256,
        ),
        last_evaluation_epoch=None,
        current_candidate_id=None,
        current_candidate_sha256=None,
        current_release_revision=None,
        current_select_input_id=None,
        current_revoked=False,
        current_revocation_record_id=None,
    )


def _event_state_root(
    previous: bytes,
    revision: int,
    artifacts: _AuthenticatedEventArtifactsV3,
) -> bytes:
    kind = b"\x01" if artifacts.event_kind is ReleaseStateEventKindV3.SELECT else b"\x02"
    record_id = artifacts.revocation_record_id or bytes(32)
    payload = (
        previous
        + _u64be(revision)
        + kind
        + artifacts.selector_input_id
        + artifacts.candidate.candidate_id
        + artifacts.candidate_sha256
        + _u64be(artifacts.release_revision)
        + _u64be(artifacts.evaluation_epoch)
        + record_id
        + artifacts.authentication_evidence_sha256
    )
    return _domain_hash(_EVENT_STATE_DOMAIN_V3, payload)


def _cursor_storage_values(
    cursor: SpotV7AuthenticatedReleaseStateCursorV3,
) -> tuple[object, ...]:
    return (
        _u64be(cursor.database_revision),
        cursor.state_root,
        cursor.database_revision,
        _optional_u64be(cursor.last_evaluation_epoch),
        cursor.current_candidate_id,
        cursor.current_candidate_sha256,
        _optional_u64be(cursor.current_release_revision),
        cursor.current_select_input_id,
        int(cursor.current_revoked),
        cursor.current_revocation_record_id,
    )


def _meta_cursor_values(row: sqlite3.Row) -> tuple[object, ...]:
    return (
        bytes(row["database_revision_be"]),
        bytes(row["state_root"]),
        int(row["event_count"]),
        _optional_blob(row["last_evaluation_epoch_be"]),
        _optional_blob(row["current_candidate_id"]),
        _optional_blob(row["current_candidate_sha256"]),
        _optional_blob(row["current_release_revision_be"]),
        _optional_blob(row["current_select_input_id"]),
        int(row["current_revoked"]),
        _optional_blob(row["current_revocation_record_id"]),
    )


def _result(
    disposition: AuthenticatedReleaseStateDispositionV3,
    code: str,
    event_kind: ReleaseStateEventKindV3,
    selector_input_id: bytes,
    cursor: SpotV7AuthenticatedReleaseStateCursorV3,
) -> SpotV7AuthenticatedReleaseStateResultV3:
    return SpotV7AuthenticatedReleaseStateResultV3._from_store(
        disposition=disposition,
        code=code,
        event_kind=event_kind,
        selector_input_id=selector_input_id,
        cursor=cursor,
        seal=_RELEASE_STATE_RESULT_SEAL_V3,
    )


def _require_selection_envelope(
    artifacts: _AuthenticatedEventArtifactsV3,
) -> SpotV7ReleaseSelectionEnvelopeV1:
    if artifacts.selection_envelope is None:
        raise ValueError("SELECT envelope required")
    return artifacts.selection_envelope


def _require_revocation_envelope(
    artifacts: _AuthenticatedEventArtifactsV3,
) -> SpotV7ReleaseRevocationEnvelopeV1:
    if artifacts.revocation_envelope is None:
        raise ValueError("REVOKE envelope required")
    return artifacts.revocation_envelope


def _require_revocation_record(
    artifacts: _AuthenticatedEventArtifactsV3,
) -> SpotV7RevocationRecordV1:
    if artifacts.record is None:
        raise ValueError("REVOKE record required")
    return artifacts.record


def _connect_database(path: Path, busy_timeout_ms: int) -> sqlite3.Connection:
    timeout_seconds = max(1, (busy_timeout_ms + 999) // 1_000)
    connection = sqlite3.connect(path, timeout=timeout_seconds, isolation_level=None)
    try:
        connection.row_factory = sqlite3.Row
        connection.execute("PRAGMA foreign_keys = ON")
        mode = str(connection.execute("PRAGMA journal_mode = DELETE").fetchone()[0]).lower()
        if mode != "delete":
            raise ValueError("authenticated release-state journal_mode must be DELETE")
        connection.execute("PRAGMA synchronous = EXTRA")
        connection.execute(f"PRAGMA busy_timeout = {busy_timeout_ms}")
        connection.execute("PRAGMA trusted_schema = OFF")
        connection.execute("PRAGMA temp_store = MEMORY")
        if int(connection.execute("PRAGMA foreign_keys").fetchone()[0]) != 1:
            raise ValueError("authenticated release-state foreign_keys must be enabled")
        if int(connection.execute("PRAGMA synchronous").fetchone()[0]) != 3:
            raise ValueError("authenticated release-state synchronous must be EXTRA")
        if int(connection.execute("PRAGMA trusted_schema").fetchone()[0]) != 0:
            raise ValueError("authenticated release-state trusted_schema must be disabled")
        if int(connection.execute("PRAGMA busy_timeout").fetchone()[0]) != busy_timeout_ms:
            raise ValueError("authenticated release-state busy_timeout mismatch")
    except (sqlite3.Error, ValueError):
        connection.close()
        raise
    return connection


def _validate_store_path(path: Path, busy_timeout_ms: int) -> None:
    if not isinstance(path, Path):
        raise TypeError("authenticated release-state path must be pathlib.Path")
    if not path.is_absolute():
        raise ValueError("authenticated release-state path must be absolute")
    if path.resolve(strict=False) != path:
        raise ValueError("authenticated release-state path must be canonical and symlink-free")
    if type(busy_timeout_ms) is not int or not 1 <= busy_timeout_ms <= MAX_BUSY_TIMEOUT_MS_V3:
        raise ValueError("authenticated release-state busy_timeout_ms is out of range")
    parent_stat = path.parent.stat(follow_symlinks=False)
    if not stat.S_ISDIR(parent_stat.st_mode):
        raise ValueError("authenticated release-state parent is not a directory")
    if parent_stat.st_uid != os.getuid() or stat.S_IMODE(parent_stat.st_mode) & 0o077:
        raise ValueError("authenticated release-state parent must be private and owned by this uid")


def _create_private_database_file(path: Path) -> bool:
    flags = os.O_RDWR | os.O_CREAT | os.O_EXCL | getattr(os, "O_CLOEXEC", 0)
    flags |= getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags, 0o600)
    except FileExistsError:
        _validate_database_file(path)
        return False
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    _validate_database_file(path)
    return True


def _validate_database_file(path: Path) -> None:
    file_stat = path.stat(follow_symlinks=False)
    if not stat.S_ISREG(file_stat.st_mode):
        raise ValueError("authenticated release-state database is not a regular file")
    if file_stat.st_uid != os.getuid() or stat.S_IMODE(file_stat.st_mode) != 0o600:
        raise ValueError(
            "authenticated release-state database must be private and owned by this uid"
        )
    if file_stat.st_nlink != 1:
        raise ValueError("authenticated release-state database must have exactly one hard link")


def _fsync_directory(path: Path) -> None:
    descriptor = os.open(
        path,
        os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_CLOEXEC", 0),
    )
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _require_token(value: object, *, name: str) -> str:
    if type(value) is not str or _TOKEN_RE.fullmatch(value) is None:
        raise ValueError(f"{name} must be a bounded ASCII token")
    return value


def _require_root(value: object, *, name: str) -> str:
    if type(value) is not str or _ROOT_RE.fullmatch(value) is None:
        raise ValueError(f"{name} must be canonical lowercase 0x hex")
    if value == "0x" + ("00" * 32):
        raise ValueError(f"{name} must be nonzero")
    return value


def _require_digest(value: object, *, name: str) -> bytes:
    if type(value) is not bytes or len(value) != 32 or not any(value):
        raise ValueError(f"{name} must be a nonzero 32-byte digest")
    return value


def _require_u64(value: object, *, name: str) -> int:
    if type(value) is not int or not 0 <= value <= MAX_U64_V3:
        raise ValueError(f"{name} must be a u64")
    return value


def _require_positive_u64(value: object, *, name: str) -> int:
    output = _require_u64(value, name=name)
    if output == 0:
        raise ValueError(f"{name} must be positive")
    return output


def _require_optional_u64(value: object, *, name: str) -> int | None:
    if value is None:
        return None
    return _require_u64(value, name=name)


def _u64be(value: int) -> bytes:
    return _require_u64(value, name="u64").to_bytes(8, "big")


def _optional_u64be(value: int | None) -> bytes | None:
    return None if value is None else _u64be(value)


def _optional_blob(value: object) -> bytes | None:
    if value is None:
        return None
    if type(value) is not bytes:
        raise ValueError("stored value must be a blob")
    return value


def _root_text(value: bytes) -> str:
    return "0x" + _require_digest(value, name="root").hex()


def _domain_hash(domain: bytes, payload: bytes) -> bytes:
    return hashlib.sha256(
        len(domain).to_bytes(2, "big") + domain + len(payload).to_bytes(8, "big") + payload
    ).digest()


def _normalize_sql(value: str) -> str:
    return " ".join(value.strip().removesuffix(";").split())


__all__ = [
    "AuthenticatedReleaseStateDispositionV3",
    "ReleaseStateEventKindV3",
    "SQLiteSpotV7AuthenticatedReleaseStateStoreV3",
    "SpotV7AuthenticatedReleaseStateCursorV3",
    "SpotV7AuthenticatedReleaseStateDurabilityUncertainV3",
    "SpotV7AuthenticatedReleaseStateResultV3",
    "SpotV7AuthenticatedReleaseStateStoreErrorV3",
    "SpotV7AuthenticatedReleaseStateStoreIdentityV3",
    "SPOT_V7_AUTHENTICATED_RELEASE_STATE_MONOTONIC_ANCHOR_BLOCKER_V3",
    "SPOT_V7_AUTHENTICATED_RELEASE_STATE_SAME_UID_BLOCKER_V3",
    "SPOT_V7_AUTHENTICATED_RELEASE_STATE_TRUST_ROOT_GOVERNANCE_BLOCKER_V3",
    "SPOT_V7_DERIVED_STATIC_TRUST_PIN_IDENTITY_ALGORITHM_V3",
    "SPOT_V7_REVOCATION_DERIVED_STATIC_TRUST_PIN_DOMAIN_V3",
    "SPOT_V7_SELECTION_DERIVED_STATIC_TRUST_PIN_DOMAIN_V3",
    "derive_revocation_static_trust_pin_identity_v3",
    "derive_selection_static_trust_pin_identity_v3",
]
