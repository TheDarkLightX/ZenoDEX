"""Durable authority-neutral store for authenticated Spot V7 selections.

The store accepts only the private result produced by the exact release-selection
quorum adapter.  Every committed event retains the complete authenticated input
closure and is cryptographically replayed when the database is opened or read.
The independently supplied store identity pins the static scope, signer registry,
and rollback/revocation policy roots.

V2 intentionally supports authenticated SELECT events only.  There is no signed
revocation capability in this profile, so revocation and every release/runtime/
settlement/production authority claim remain false.

The self-authenticating local history does not prove monotonic storage.  An older
internally valid database snapshot can be restored unless an independently
governed monotonic state anchor is checked by a later authority-bearing profile.
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
from typing import Any, Final, Mapping, NoReturn, Sequence, SupportsIndex, cast, final

from src.integration._zrpf_spot_v7_release_selection_envelope_v1 import (
    SpotV7ReleaseSelectionEnvelopeV1,
    parse_exact_spot_v7_release_selection_envelope_v1,
)
from src.integration.zrpf_spot_v7_authenticated_release_selection_v1 import (
    SPOT_V7_RELEASE_SELECTION_AUTHENTICATION_EVIDENCE_SCHEMA_V1,
    SpotV7ReleaseSelectionExternalTrustPinsV1,
    _AuthenticatedReleaseSelectionDurableArtifactsV2,
    _AuthenticatedSpotV7ReleaseSelectionV1,
    authenticate_spot_v7_release_selection_v1,
)
from src.state.canonical import canonical_json_bytes
from tools.zrpf_spot_v7_governed_release_selector_input_v1 import (
    SELECTOR_INPUT_BYTES_V1,
    GovernedReleaseSelectorInputV1,
    SelectorOperationV1,
    parse_exact_governed_release_selector_input_v1,
)
from tools.zrpf_spot_v7_release_candidate_manifest_v1 import (
    SPOT_V7_RELEASE_PROFILE_V1,
    SpotV7ReleaseCandidateManifestV1,
    check_exact_spot_v7_release_candidate_manifest_v1,
)

STORE_SCHEMA_VERSION_V2: Final = 2
STORE_APPLICATION_ID_V2: Final = 0x5A525632
DEFAULT_BUSY_TIMEOUT_MS_V2: Final = 5_000
MAX_BUSY_TIMEOUT_MS_V2: Final = 60_000
MAX_AUTHENTICATED_SELECTION_EVENTS_V2: Final = 4_096
MAX_STORE_IDENTITY_BYTES_V2: Final = 16 * 1_024
MAX_AUTHENTICATION_EVIDENCE_BYTES_V2: Final = 2 * 1_024 * 1_024
MAX_SIGNATURE_SET_BYTES_V2: Final = 1 * 1_024 * 1_024
MAX_QUORUM_REPORT_BYTES_V2: Final = 256 * 1_024
MAX_EXTERNAL_TRUST_PINS_BYTES_V2: Final = 16 * 1_024
MAX_JSON_DEPTH_V2: Final = 12
MAX_U64_V2: Final = (1 << 64) - 1

SPOT_V7_AUTHENTICATED_RELEASE_SELECTION_STORE_IDENTITY_SCHEMA_V2: Final = (
    "zenodex.zrpf.spot_v7.authenticated_release_selection_store_identity.v2"
)
SPOT_V7_AUTHENTICATED_RELEASE_SELECTION_REVOCATION_BLOCKER_V2: Final = (
    "SIGNED_RELEASE_REVOCATION_CAPABILITY_REQUIRED"
)
SPOT_V7_AUTHENTICATED_RELEASE_SELECTION_MONOTONIC_ANCHOR_BLOCKER_V2: Final = (
    "EXTERNAL_MONOTONIC_RELEASE_STATE_ANCHOR_REQUIRED"
)
SPOT_V7_AUTHENTICATED_RELEASE_SELECTION_SAME_UID_BLOCKER_V2: Final = (
    "DEDICATED_STORAGE_SUPERVISOR_REQUIRED"
)

_GENESIS_STATE_DOMAIN_V2: Final = b"zenodex.zrpf.spot_v7.auth_selection.genesis.v2"
_EVENT_STATE_DOMAIN_V2: Final = b"zenodex.zrpf.spot_v7.auth_selection.event.v2"
_TOKEN_RE: Final = re.compile(r"^[A-Za-z0-9._:-]{1,128}$")
_ROOT_RE: Final = re.compile(r"^0x[0-9a-f]{64}$")

_EVIDENCE_FIELDS_V1: Final = frozenset(
    {
        "candidate_bytes_hex",
        "external_trust_pins",
        "release_selection_envelope_hex",
        "schema",
        "selector_input_bytes_hex",
        "selector_input_id",
        "signature_envelopes",
        "signature_quorum_report",
        "signer_registry",
    }
)
_PINS_FIELDS_V1: Final = frozenset(
    {
        "application_id",
        "chain_id",
        "domain_id",
        "expected_current_candidate_id",
        "expected_current_select_input_id",
        "expected_database_revision",
        "expected_quorum_threshold",
        "expected_signer_registry_hash",
        "minimum_target_release_revision",
        "release_profile",
        "revocation_policy_root",
        "revocation_registry_root",
        "rollback_policy_root",
        "signer_registry_activation_epoch",
        "signer_registry_id",
        "signer_registry_revision",
        "signer_registry_revocation_epoch",
        "trusted_evaluation_epoch",
    }
)


class AuthenticatedReleaseSelectionDispositionV2(str, Enum):
    COMMITTED = "committed"
    IDEMPOTENT = "idempotent_exact_replay"
    REJECTED = "rejected"


class SpotV7AuthenticatedReleaseSelectionStoreErrorV2(RuntimeError):
    """Storage or history-integrity failure, distinct from a governed reject."""

    def __init__(self, code: str, detail: str) -> None:
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}")


@final
class SpotV7AuthenticatedReleaseSelectionDurabilityUncertainV2(
    SpotV7AuthenticatedReleaseSelectionStoreErrorV2
):
    """A commit started, but exact durable outcome could not be established."""

    def __init__(self, *, selector_input_id: bytes, detail: str) -> None:
        self.selector_input_id = selector_input_id
        super().__init__("POST_COMMIT_DURABILITY_UNCERTAIN", detail)

    @property
    def candidate_selected(self) -> bool:
        return False

    @property
    def revocation_authority(self) -> bool:
        return False

    @property
    def revocation_blocker_code(self) -> str:
        return SPOT_V7_AUTHENTICATED_RELEASE_SELECTION_REVOCATION_BLOCKER_V2

    @property
    def monotonic_state_anchor_verified(self) -> bool:
        return False

    @property
    def monotonic_state_anchor_blocker_code(self) -> str:
        return SPOT_V7_AUTHENTICATED_RELEASE_SELECTION_MONOTONIC_ANCHOR_BLOCKER_V2

    @property
    def same_uid_path_substitution_resistance_established(self) -> bool:
        return False

    @property
    def same_uid_path_substitution_blocker_code(self) -> str:
        return SPOT_V7_AUTHENTICATED_RELEASE_SELECTION_SAME_UID_BLOCKER_V2

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


class _SelectionRejectV2(ValueError):
    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(code)


@final
@dataclass(frozen=True, slots=True)
class SpotV7AuthenticatedReleaseSelectionStoreIdentityV2:
    """Independent static expectations fixed at database genesis."""

    application_id: str
    chain_id: str
    domain_id: str
    release_profile: str
    signer_registry_id: str
    expected_signer_registry_hash: str
    expected_signer_registry_revision: int
    signer_registry_activation_epoch: int
    signer_registry_revocation_epoch: int | None
    expected_quorum_threshold: int
    rollback_policy_root: bytes
    revocation_policy_root: bytes
    revocation_registry_root: bytes
    external_trust_pin_identity: bytes

    def __post_init__(self) -> None:
        _require_token(self.application_id, name="application_id")
        _require_token(self.chain_id, name="chain_id")
        _require_token(self.domain_id, name="domain_id")
        _require_token(self.release_profile, name="release_profile")
        if self.release_profile != SPOT_V7_RELEASE_PROFILE_V1:
            raise ValueError("authenticated selection store requires Spot V7 release profile")
        if self.chain_id == self.domain_id:
            raise ValueError("authenticated selection store chain and domain must differ")
        _require_token(self.signer_registry_id, name="signer_registry_id")
        _require_root(self.expected_signer_registry_hash, name="expected_signer_registry_hash")
        _require_positive_u64(
            self.expected_signer_registry_revision,
            name="expected_signer_registry_revision",
        )
        activation = _require_u64(
            self.signer_registry_activation_epoch,
            name="signer_registry_activation_epoch",
        )
        revocation = _require_optional_u64(
            self.signer_registry_revocation_epoch,
            name="signer_registry_revocation_epoch",
        )
        if revocation is not None and revocation <= activation:
            raise ValueError("signer registry revocation must follow activation")
        _require_positive_u64(
            self.expected_quorum_threshold,
            name="expected_quorum_threshold",
        )
        _require_digest(self.rollback_policy_root, name="rollback_policy_root")
        _require_digest(self.revocation_policy_root, name="revocation_policy_root")
        _require_digest(self.revocation_registry_root, name="revocation_registry_root")
        _require_digest(
            self.external_trust_pin_identity,
            name="external_trust_pin_identity",
        )

    @property
    def canonical_bytes(self) -> bytes:
        return canonical_json_bytes(
            {
                "application_id": self.application_id,
                "chain_id": self.chain_id,
                "domain_id": self.domain_id,
                "expected_quorum_threshold": self.expected_quorum_threshold,
                "expected_signer_registry_hash": self.expected_signer_registry_hash,
                "expected_signer_registry_revision": self.expected_signer_registry_revision,
                "external_trust_pin_identity": "0x" + self.external_trust_pin_identity.hex(),
                "monotonic_state_anchor_verified": False,
                "same_uid_path_substitution_resistance_established": False,
                "release_profile": self.release_profile,
                "revocation_policy_root": "0x" + self.revocation_policy_root.hex(),
                "revocation_registry_root": "0x" + self.revocation_registry_root.hex(),
                "rollback_policy_root": "0x" + self.rollback_policy_root.hex(),
                "schema": SPOT_V7_AUTHENTICATED_RELEASE_SELECTION_STORE_IDENTITY_SCHEMA_V2,
                "signer_registry_activation_epoch": self.signer_registry_activation_epoch,
                "signer_registry_id": self.signer_registry_id,
                "signer_registry_revocation_epoch": self.signer_registry_revocation_epoch,
            }
        )

    @property
    def identity_sha256(self) -> bytes:
        return hashlib.sha256(self.canonical_bytes).digest()

    @property
    def release_governed_trust_pin_authenticated(self) -> bool:
        return False

    @property
    def monotonic_state_anchor_verified(self) -> bool:
        return False

    @property
    def monotonic_state_anchor_blocker_code(self) -> str:
        return SPOT_V7_AUTHENTICATED_RELEASE_SELECTION_MONOTONIC_ANCHOR_BLOCKER_V2

    @property
    def same_uid_path_substitution_resistance_established(self) -> bool:
        return False

    @property
    def same_uid_path_substitution_blocker_code(self) -> str:
        return SPOT_V7_AUTHENTICATED_RELEASE_SELECTION_SAME_UID_BLOCKER_V2

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


@final
@dataclass(frozen=True, slots=True)
class SpotV7AuthenticatedReleaseSelectionCursorV2:
    database_revision: int
    state_root: bytes
    last_evaluation_epoch: int | None
    current_candidate_id: bytes | None
    current_candidate_sha256: bytes | None
    current_release_revision: int | None
    current_selector_input_id: bytes | None

    @property
    def candidate_selected(self) -> bool:
        return False

    @property
    def revocation_authority(self) -> bool:
        return False

    @property
    def revocation_blocker_code(self) -> str:
        return SPOT_V7_AUTHENTICATED_RELEASE_SELECTION_REVOCATION_BLOCKER_V2

    @property
    def monotonic_state_anchor_verified(self) -> bool:
        return False

    @property
    def monotonic_state_anchor_blocker_code(self) -> str:
        return SPOT_V7_AUTHENTICATED_RELEASE_SELECTION_MONOTONIC_ANCHOR_BLOCKER_V2

    @property
    def same_uid_path_substitution_resistance_established(self) -> bool:
        return False

    @property
    def same_uid_path_substitution_blocker_code(self) -> str:
        return SPOT_V7_AUTHENTICATED_RELEASE_SELECTION_SAME_UID_BLOCKER_V2

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


class _AuthenticatedReleaseSelectionResultSealV2:
    __slots__ = ()


_AUTHENTICATED_RELEASE_SELECTION_RESULT_SEAL_V2: Final = (
    _AuthenticatedReleaseSelectionResultSealV2()
)


@final
class SpotV7AuthenticatedReleaseSelectionResultV2:
    """Opaque authority-neutral status returned only by the authenticated store."""

    __slots__ = ("_code", "_cursor", "_disposition", "_selector_input_id")
    _code: str
    _cursor: SpotV7AuthenticatedReleaseSelectionCursorV2
    _disposition: AuthenticatedReleaseSelectionDispositionV2
    _selector_input_id: bytes | None

    def __new__(
        cls, *_args: object, **_kwargs: object
    ) -> SpotV7AuthenticatedReleaseSelectionResultV2:
        raise TypeError(
            "authenticated selection status requires the module-private store result seal"
        )

    @classmethod
    def _from_store(
        cls,
        *,
        disposition: AuthenticatedReleaseSelectionDispositionV2,
        code: str,
        selector_input_id: bytes | None,
        cursor: SpotV7AuthenticatedReleaseSelectionCursorV2,
        seal: _AuthenticatedReleaseSelectionResultSealV2,
    ) -> SpotV7AuthenticatedReleaseSelectionResultV2:
        if seal is not _AUTHENTICATED_RELEASE_SELECTION_RESULT_SEAL_V2:
            raise TypeError(
                "authenticated selection status requires the module-private store result seal"
            )
        if type(disposition) is not AuthenticatedReleaseSelectionDispositionV2:
            raise TypeError("authenticated selection disposition must use the exact V2 enum")
        normalized_code = _require_token(code, name="authenticated_selection_result.code")
        if selector_input_id is None:
            normalized_selector_input_id = None
        else:
            normalized_selector_input_id = _require_digest(
                selector_input_id,
                name="authenticated_selection_result.selector_input_id",
            )
        if type(cursor) is not SpotV7AuthenticatedReleaseSelectionCursorV2:
            raise TypeError("authenticated selection result cursor must use the exact V2 cursor")
        value = object.__new__(cls)
        object.__setattr__(value, "_disposition", disposition)
        object.__setattr__(value, "_code", normalized_code)
        object.__setattr__(value, "_selector_input_id", normalized_selector_input_id)
        object.__setattr__(value, "_cursor", cursor)
        return value

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("authenticated selection status cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("authenticated selection status is immutable")

    def __delattr__(self, _name: str) -> NoReturn:
        raise TypeError("authenticated selection status is immutable")

    def __bool__(self) -> NoReturn:
        raise TypeError("authenticated selection status requires explicit disposition handling")

    def __copy__(self) -> NoReturn:
        raise TypeError("authenticated selection status cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("authenticated selection status cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("authenticated selection status cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("authenticated selection status cannot be serialized")

    def __getstate__(self) -> NoReturn:
        raise TypeError("authenticated selection status cannot be serialized")

    @property
    def disposition(self) -> AuthenticatedReleaseSelectionDispositionV2:
        return self._disposition

    @property
    def code(self) -> str:
        return self._code

    @property
    def selector_input_id(self) -> bytes | None:
        return self._selector_input_id

    @property
    def cursor(self) -> SpotV7AuthenticatedReleaseSelectionCursorV2:
        return self._cursor

    @property
    def candidate_selected(self) -> bool:
        return False

    @property
    def revocation_authority(self) -> bool:
        return False

    @property
    def revocation_blocker_code(self) -> str:
        return SPOT_V7_AUTHENTICATED_RELEASE_SELECTION_REVOCATION_BLOCKER_V2

    @property
    def monotonic_state_anchor_verified(self) -> bool:
        return False

    @property
    def monotonic_state_anchor_blocker_code(self) -> str:
        return SPOT_V7_AUTHENTICATED_RELEASE_SELECTION_MONOTONIC_ANCHOR_BLOCKER_V2

    @property
    def same_uid_path_substitution_resistance_established(self) -> bool:
        return False

    @property
    def same_uid_path_substitution_blocker_code(self) -> str:
        return SPOT_V7_AUTHENTICATED_RELEASE_SELECTION_SAME_UID_BLOCKER_V2

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


@dataclass(frozen=True, slots=True)
class _AuthenticatedArtifactsV2:
    selector: GovernedReleaseSelectorInputV1
    candidate: SpotV7ReleaseCandidateManifestV1
    envelope: SpotV7ReleaseSelectionEnvelopeV1
    selector_input_bytes: bytes
    candidate_bytes: bytes
    signed_envelope_bytes: bytes
    signer_registry_bytes: bytes
    signature_envelopes_bytes: bytes
    quorum_report_bytes: bytes
    external_trust_pins_bytes: bytes
    authentication_evidence_bytes: bytes
    signed_envelope_sha256: bytes
    signer_registry_sha256: bytes
    signature_envelopes_sha256: bytes
    quorum_report_sha256: bytes
    quorum_report_hash: bytes
    external_trust_pins_sha256: bytes
    authentication_evidence_sha256: bytes
    activation_epoch: int
    expiration_epoch: int | None
    parent_candidate_id: bytes | None


_SCHEMA_STATEMENTS_V2: Final = (
    """
    CREATE TABLE spot_v7_authenticated_release_selection_meta_v2 (
        singleton INTEGER NOT NULL PRIMARY KEY CHECK (singleton = 1),
        schema_version INTEGER NOT NULL CHECK (schema_version = 2),
        store_identity_bytes BLOB NOT NULL CHECK (typeof(store_identity_bytes) = 'blob' AND length(store_identity_bytes) BETWEEN 1 AND 16384),
        store_identity_sha256 BLOB NOT NULL CHECK (typeof(store_identity_sha256) = 'blob' AND length(store_identity_sha256) = 32),
        external_trust_pin_identity BLOB NOT NULL CHECK (typeof(external_trust_pin_identity) = 'blob' AND length(external_trust_pin_identity) = 32),
        expected_signer_registry_hash BLOB NOT NULL CHECK (typeof(expected_signer_registry_hash) = 'blob' AND length(expected_signer_registry_hash) = 32),
        expected_signer_registry_revision_be BLOB NOT NULL CHECK (typeof(expected_signer_registry_revision_be) = 'blob' AND length(expected_signer_registry_revision_be) = 8),
        rollback_policy_root BLOB NOT NULL CHECK (typeof(rollback_policy_root) = 'blob' AND length(rollback_policy_root) = 32),
        revocation_policy_root BLOB NOT NULL CHECK (typeof(revocation_policy_root) = 'blob' AND length(revocation_policy_root) = 32),
        revocation_registry_root BLOB NOT NULL CHECK (typeof(revocation_registry_root) = 'blob' AND length(revocation_registry_root) = 32),
        database_revision_be BLOB NOT NULL CHECK (typeof(database_revision_be) = 'blob' AND length(database_revision_be) = 8),
        state_root BLOB NOT NULL CHECK (typeof(state_root) = 'blob' AND length(state_root) = 32),
        event_count INTEGER NOT NULL CHECK (event_count BETWEEN 0 AND 4096),
        last_evaluation_epoch_be BLOB CHECK (last_evaluation_epoch_be IS NULL OR (typeof(last_evaluation_epoch_be) = 'blob' AND length(last_evaluation_epoch_be) = 8)),
        current_candidate_id BLOB CHECK (current_candidate_id IS NULL OR (typeof(current_candidate_id) = 'blob' AND length(current_candidate_id) = 32)),
        current_candidate_sha256 BLOB CHECK (current_candidate_sha256 IS NULL OR (typeof(current_candidate_sha256) = 'blob' AND length(current_candidate_sha256) = 32)),
        current_release_revision_be BLOB CHECK (current_release_revision_be IS NULL OR (typeof(current_release_revision_be) = 'blob' AND length(current_release_revision_be) = 8)),
        current_selector_input_id BLOB CHECK (current_selector_input_id IS NULL OR (typeof(current_selector_input_id) = 'blob' AND length(current_selector_input_id) = 32)),
        release_authority INTEGER NOT NULL CHECK (release_authority = 0),
        runtime_authority INTEGER NOT NULL CHECK (runtime_authority = 0),
        settlement_authority INTEGER NOT NULL CHECK (settlement_authority = 0),
        production_authority INTEGER NOT NULL CHECK (production_authority = 0),
        CHECK (
            (event_count = 0 AND last_evaluation_epoch_be IS NULL AND current_candidate_id IS NULL AND current_candidate_sha256 IS NULL AND current_release_revision_be IS NULL AND current_selector_input_id IS NULL)
            OR
            (event_count > 0 AND last_evaluation_epoch_be IS NOT NULL AND current_candidate_id IS NOT NULL AND current_candidate_sha256 IS NOT NULL AND current_release_revision_be IS NOT NULL AND current_selector_input_id IS NOT NULL)
        )
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE spot_v7_authenticated_release_selection_events_v2 (
        event_revision_be BLOB NOT NULL PRIMARY KEY CHECK (typeof(event_revision_be) = 'blob' AND length(event_revision_be) = 8),
        selector_input_id BLOB NOT NULL UNIQUE CHECK (typeof(selector_input_id) = 'blob' AND length(selector_input_id) = 32),
        selector_input_bytes BLOB NOT NULL CHECK (typeof(selector_input_bytes) = 'blob' AND length(selector_input_bytes) = 320),
        candidate_id BLOB NOT NULL UNIQUE CHECK (typeof(candidate_id) = 'blob' AND length(candidate_id) = 32),
        candidate_sha256 BLOB NOT NULL CHECK (typeof(candidate_sha256) = 'blob' AND length(candidate_sha256) = 32),
        candidate_bytes BLOB NOT NULL CHECK (typeof(candidate_bytes) = 'blob' AND length(candidate_bytes) BETWEEN 1 AND 262144),
        release_revision_be BLOB NOT NULL UNIQUE CHECK (typeof(release_revision_be) = 'blob' AND length(release_revision_be) = 8),
        evaluation_epoch_be BLOB NOT NULL CHECK (typeof(evaluation_epoch_be) = 'blob' AND length(evaluation_epoch_be) = 8),
        signed_envelope_bytes BLOB NOT NULL CHECK (typeof(signed_envelope_bytes) = 'blob' AND length(signed_envelope_bytes) BETWEEN 1 AND 16384),
        signed_envelope_sha256 BLOB NOT NULL CHECK (typeof(signed_envelope_sha256) = 'blob' AND length(signed_envelope_sha256) = 32),
        signer_registry_bytes BLOB NOT NULL CHECK (typeof(signer_registry_bytes) = 'blob' AND length(signer_registry_bytes) BETWEEN 1 AND 262144),
        signer_registry_sha256 BLOB NOT NULL CHECK (typeof(signer_registry_sha256) = 'blob' AND length(signer_registry_sha256) = 32),
        signer_registry_hash BLOB NOT NULL CHECK (typeof(signer_registry_hash) = 'blob' AND length(signer_registry_hash) = 32),
        signer_registry_revision_be BLOB NOT NULL CHECK (typeof(signer_registry_revision_be) = 'blob' AND length(signer_registry_revision_be) = 8),
        signature_envelopes_bytes BLOB NOT NULL CHECK (typeof(signature_envelopes_bytes) = 'blob' AND length(signature_envelopes_bytes) BETWEEN 1 AND 1048576),
        signature_envelopes_sha256 BLOB NOT NULL CHECK (typeof(signature_envelopes_sha256) = 'blob' AND length(signature_envelopes_sha256) = 32),
        quorum_report_bytes BLOB NOT NULL CHECK (typeof(quorum_report_bytes) = 'blob' AND length(quorum_report_bytes) BETWEEN 1 AND 262144),
        quorum_report_sha256 BLOB NOT NULL CHECK (typeof(quorum_report_sha256) = 'blob' AND length(quorum_report_sha256) = 32),
        quorum_report_hash BLOB NOT NULL CHECK (typeof(quorum_report_hash) = 'blob' AND length(quorum_report_hash) = 32),
        external_trust_pins_bytes BLOB NOT NULL CHECK (typeof(external_trust_pins_bytes) = 'blob' AND length(external_trust_pins_bytes) BETWEEN 1 AND 16384),
        external_trust_pins_sha256 BLOB NOT NULL CHECK (typeof(external_trust_pins_sha256) = 'blob' AND length(external_trust_pins_sha256) = 32),
        external_trust_pin_identity BLOB NOT NULL CHECK (typeof(external_trust_pin_identity) = 'blob' AND length(external_trust_pin_identity) = 32),
        authentication_evidence_bytes BLOB NOT NULL CHECK (typeof(authentication_evidence_bytes) = 'blob' AND length(authentication_evidence_bytes) BETWEEN 1 AND 2097152),
        authentication_evidence_sha256 BLOB NOT NULL UNIQUE CHECK (typeof(authentication_evidence_sha256) = 'blob' AND length(authentication_evidence_sha256) = 32),
        previous_state_root BLOB NOT NULL CHECK (typeof(previous_state_root) = 'blob' AND length(previous_state_root) = 32),
        result_state_root BLOB NOT NULL UNIQUE CHECK (typeof(result_state_root) = 'blob' AND length(result_state_root) = 32),
        durable_authenticated_selection_recorded INTEGER NOT NULL CHECK (durable_authenticated_selection_recorded = 1),
        revocation_authority INTEGER NOT NULL CHECK (revocation_authority = 0),
        release_authority INTEGER NOT NULL CHECK (release_authority = 0),
        runtime_authority INTEGER NOT NULL CHECK (runtime_authority = 0),
        settlement_authority INTEGER NOT NULL CHECK (settlement_authority = 0),
        production_authority INTEGER NOT NULL CHECK (production_authority = 0)
    ) STRICT, WITHOUT ROWID
    """,
)

_EXPECTED_SCHEMA_SQL_V2: Final = {
    "spot_v7_authenticated_release_selection_events_v2": _SCHEMA_STATEMENTS_V2[1],
    "spot_v7_authenticated_release_selection_meta_v2": _SCHEMA_STATEMENTS_V2[0],
}


@final
class SQLiteSpotV7AuthenticatedReleaseSelectionStoreV2:
    """Fsync-backed authenticated selection history with no authority mint."""

    __slots__ = ("_busy_timeout_ms", "_identity", "_path")

    def __init__(
        self,
        path: Path,
        *,
        identity: SpotV7AuthenticatedReleaseSelectionStoreIdentityV2,
        busy_timeout_ms: int = DEFAULT_BUSY_TIMEOUT_MS_V2,
    ) -> None:
        _validate_store_path(path, busy_timeout_ms)
        if type(identity) is not SpotV7AuthenticatedReleaseSelectionStoreIdentityV2:
            raise TypeError("authenticated selection store requires exact V2 identity")
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
            raise SpotV7AuthenticatedReleaseSelectionStoreErrorV2(
                "STORE_OPEN_FAILED", str(exc)
            ) from exc

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("SQLiteSpotV7AuthenticatedReleaseSelectionStoreV2 cannot be subclassed")

    @property
    def path(self) -> Path:
        return self._path

    @property
    def identity(self) -> SpotV7AuthenticatedReleaseSelectionStoreIdentityV2:
        return self._identity

    @property
    def revocation_blocker_code(self) -> str:
        return SPOT_V7_AUTHENTICATED_RELEASE_SELECTION_REVOCATION_BLOCKER_V2

    @property
    def monotonic_state_anchor_verified(self) -> bool:
        return False

    @property
    def monotonic_state_anchor_blocker_code(self) -> str:
        return SPOT_V7_AUTHENTICATED_RELEASE_SELECTION_MONOTONIC_ANCHOR_BLOCKER_V2

    @property
    def same_uid_path_substitution_resistance_established(self) -> bool:
        return False

    @property
    def same_uid_path_substitution_blocker_code(self) -> str:
        return SPOT_V7_AUTHENTICATED_RELEASE_SELECTION_SAME_UID_BLOCKER_V2

    def read_cursor(self) -> SpotV7AuthenticatedReleaseSelectionCursorV2:
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
            raise SpotV7AuthenticatedReleaseSelectionStoreErrorV2(
                "STORE_READ_FAILED", str(exc)
            ) from exc
        finally:
            if connection is not None:
                connection.close()

    def commit(
        self,
        authenticated_selection: _AuthenticatedSpotV7ReleaseSelectionV1,
    ) -> SpotV7AuthenticatedReleaseSelectionResultV2:
        """Atomically append one exact authenticated forward selection."""

        if type(authenticated_selection) is not _AuthenticatedSpotV7ReleaseSelectionV1:
            raise TypeError("store requires exact authenticated release-selection capability")
        if not authenticated_selection._has_private_seal():
            raise TypeError("store requires sealed authenticated release-selection capability")
        projection = _capability_durable_projection(authenticated_selection)
        try:
            artifacts = _revalidate_authentication_evidence(
                projection.authentication_evidence_bytes
            )
            _require_projection_matches_artifacts(projection, artifacts)
            _require_capability_matches_artifacts(authenticated_selection, artifacts)
            _require_store_identity_matches_artifacts(self._identity, artifacts)
        except (TypeError, ValueError) as exc:
            raise SpotV7AuthenticatedReleaseSelectionStoreErrorV2(
                "AUTHENTICATED_SELECTION_INVALID", str(exc)
            ) from exc

        connection: sqlite3.Connection | None = None
        commit_started = False
        try:
            connection = self._connect()
            connection.execute("BEGIN IMMEDIATE")
            _validate_schema(connection)
            cursor = _validate_complete_history(connection, self._identity)
            existing = _read_event_by_selector_id(connection, artifacts.selector.input_id)
            if existing is not None:
                result = _resolve_exact_replay(existing, artifacts, cursor, self._identity)
                connection.rollback()
                return result
            try:
                next_cursor = _apply_forward_transition(cursor, artifacts)
            except _SelectionRejectV2 as exc:
                connection.rollback()
                return _result(
                    AuthenticatedReleaseSelectionDispositionV2.REJECTED,
                    exc.code,
                    artifacts.selector.input_id,
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
                AuthenticatedReleaseSelectionDispositionV2.COMMITTED,
                "AUTHENTICATED_SELECT_COMMITTED",
                artifacts.selector.input_id,
                next_cursor,
            )
        except SpotV7AuthenticatedReleaseSelectionStoreErrorV2:
            if connection is not None and connection.in_transaction:
                connection.rollback()
            raise
        except (OSError, sqlite3.Error, TypeError, ValueError) as exc:
            if connection is not None and connection.in_transaction:
                connection.rollback()
            if commit_started:
                return self._resolve_post_commit(artifacts, exc)
            raise SpotV7AuthenticatedReleaseSelectionStoreErrorV2(
                "STORE_COMMIT_FAILED", str(exc)
            ) from exc
        finally:
            if connection is not None:
                connection.close()

    def _rejected(self, code: str) -> SpotV7AuthenticatedReleaseSelectionResultV2:
        return _result(
            AuthenticatedReleaseSelectionDispositionV2.REJECTED,
            code,
            None,
            self.read_cursor(),
        )

    def _resolve_post_commit(
        self,
        artifacts: _AuthenticatedArtifactsV2,
        error: BaseException,
    ) -> SpotV7AuthenticatedReleaseSelectionResultV2:
        connection: sqlite3.Connection | None = None
        try:
            connection = self._connect()
            connection.execute("BEGIN")
            _validate_schema(connection)
            cursor = _validate_complete_history(connection, self._identity)
            row = _read_event_by_selector_id(connection, artifacts.selector.input_id)
            if row is None:
                raise ValueError("committed event is absent during post-commit resolution")
            _resolve_exact_replay(row, artifacts, cursor, self._identity)
            connection.rollback()
            return _result(
                AuthenticatedReleaseSelectionDispositionV2.COMMITTED,
                "AUTHENTICATED_SELECT_COMMITTED_POST_COMMIT_RESOLVED",
                artifacts.selector.input_id,
                cursor,
            )
        except (OSError, sqlite3.Error, TypeError, ValueError) as replay_error:
            if connection is not None and connection.in_transaction:
                connection.rollback()
            raise SpotV7AuthenticatedReleaseSelectionDurabilityUncertainV2(
                selector_input_id=artifacts.selector.input_id,
                detail=f"commit outcome unresolved after {error!r}: {replay_error!r}",
            ) from error
        finally:
            if connection is not None:
                connection.close()

    def _connect(self) -> sqlite3.Connection:
        _validate_database_file(self._path)
        return _connect_database(self._path, self._busy_timeout_ms)


def _capability_durable_projection(
    capability: _AuthenticatedSpotV7ReleaseSelectionV1,
) -> _AuthenticatedReleaseSelectionDurableArtifactsV2:
    """Obtain the revalidated bytes-only projection owned by the auth module."""

    projection = capability._artifacts_for_durable_store_v2()
    if type(projection) is not _AuthenticatedReleaseSelectionDurableArtifactsV2:
        raise TypeError("authenticated release selection returned the wrong store projection")
    return projection


def _revalidate_authentication_evidence(raw: bytes) -> _AuthenticatedArtifactsV2:
    document = _decode_exact_evidence_document(raw)
    pins_document = _require_exact_fields(
        document["external_trust_pins"],
        expected=_PINS_FIELDS_V1,
        name="external_trust_pins",
    )
    selector_input_bytes = _decode_hex_bytes(
        document["selector_input_bytes_hex"],
        name="selector_input_bytes_hex",
        exact_bytes=SELECTOR_INPUT_BYTES_V1,
    )
    selector_input_id = _decode_root_bytes(document["selector_input_id"], name="selector_input_id")
    candidate_bytes = _decode_hex_bytes(
        document["candidate_bytes_hex"],
        name="candidate_bytes_hex",
        minimum_bytes=1,
        maximum_bytes=262_144,
    )
    signed_envelope_bytes = _decode_hex_bytes(
        document["release_selection_envelope_hex"],
        name="release_selection_envelope_hex",
        minimum_bytes=1,
        maximum_bytes=16_384,
    )
    signer_registry = _require_exact_dict(document["signer_registry"], name="signer_registry")
    signatures = _require_exact_dict_sequence(
        document["signature_envelopes"],
        name="signature_envelopes",
    )
    quorum_report = _require_exact_dict(
        document["signature_quorum_report"],
        name="signature_quorum_report",
    )
    pins = _pins_from_document(pins_document)

    authenticated = authenticate_spot_v7_release_selection_v1(
        signed_envelope_bytes,
        selector_input_bytes=selector_input_bytes,
        expected_selector_input_id=selector_input_id,
        candidate_bytes=candidate_bytes,
        external_trust_pins=pins,
        trusted_signer_registry=signer_registry,
        signature_envelopes=signatures,
    )
    evidence_sha256 = hashlib.sha256(raw).digest()
    if authenticated.evidence_sha256 != evidence_sha256.hex():
        raise ValueError("stored authentication evidence does not exactly recompose")
    envelope = parse_exact_spot_v7_release_selection_envelope_v1(signed_envelope_bytes)
    selector = parse_exact_governed_release_selector_input_v1(
        selector_input_bytes,
        expected_input_id=selector_input_id,
    )
    if selector.operation is not SelectorOperationV1.SELECT:
        raise ValueError("authenticated V2 store supports SELECT events only")
    candidate = check_exact_spot_v7_release_candidate_manifest_v1(
        candidate_bytes,
        expected_candidate_id=envelope.candidate_id,
    )
    candidate_document = cast(dict[str, Any], json.loads(candidate.canonical_bytes))
    lineage = cast(dict[str, Any], candidate_document["lineage"])
    registry_bytes = canonical_json_bytes(signer_registry)
    signature_bytes = canonical_json_bytes(list(signatures))
    report_bytes = canonical_json_bytes(quorum_report)
    pins_bytes = canonical_json_bytes(pins_document)
    _require_maximum_size(
        signature_bytes,
        maximum=MAX_SIGNATURE_SET_BYTES_V2,
        name="signature_envelopes_bytes",
    )
    _require_maximum_size(
        report_bytes,
        maximum=MAX_QUORUM_REPORT_BYTES_V2,
        name="quorum_report_bytes",
    )
    _require_maximum_size(
        pins_bytes,
        maximum=MAX_EXTERNAL_TRUST_PINS_BYTES_V2,
        name="external_trust_pins_bytes",
    )
    report_hash = _decode_root_bytes(
        quorum_report.get("quorum_report_hash"),
        name="quorum_report_hash",
    )
    return _AuthenticatedArtifactsV2(
        selector=selector,
        candidate=candidate,
        envelope=envelope,
        selector_input_bytes=selector_input_bytes,
        candidate_bytes=candidate_bytes,
        signed_envelope_bytes=signed_envelope_bytes,
        signer_registry_bytes=registry_bytes,
        signature_envelopes_bytes=signature_bytes,
        quorum_report_bytes=report_bytes,
        external_trust_pins_bytes=pins_bytes,
        authentication_evidence_bytes=raw,
        signed_envelope_sha256=hashlib.sha256(signed_envelope_bytes).digest(),
        signer_registry_sha256=hashlib.sha256(registry_bytes).digest(),
        signature_envelopes_sha256=hashlib.sha256(signature_bytes).digest(),
        quorum_report_sha256=hashlib.sha256(report_bytes).digest(),
        quorum_report_hash=report_hash,
        external_trust_pins_sha256=hashlib.sha256(pins_bytes).digest(),
        authentication_evidence_sha256=evidence_sha256,
        activation_epoch=_require_u64(
            lineage["proposed_activation_epoch"],
            name="candidate_activation_epoch",
        ),
        expiration_epoch=_require_optional_u64(
            lineage["proposed_expiration_epoch"],
            name="candidate_expiration_epoch",
        ),
        parent_candidate_id=candidate.parent_candidate_id,
    )


def _require_capability_matches_artifacts(
    capability: _AuthenticatedSpotV7ReleaseSelectionV1,
    artifacts: _AuthenticatedArtifactsV2,
) -> None:
    expected = (
        artifacts.selector.input_id,
        artifacts.candidate.candidate_id,
        hashlib.sha256(artifacts.candidate_bytes).digest(),
        artifacts.candidate.release_revision,
        artifacts.selector.evaluation_epoch,
        artifacts.envelope.chain_id,
        artifacts.envelope.domain_id,
        artifacts.envelope.signer_registry_hash,
        artifacts.envelope.signer_registry_revision,
        artifacts.envelope.quorum_threshold,
        "0x" + artifacts.quorum_report_hash.hex(),
        artifacts.authentication_evidence_sha256.hex(),
    )
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
        capability.quorum_report_hash,
        capability.evidence_sha256,
    )
    if observed != expected:
        raise ValueError("authenticated capability differs from its exact evidence projection")


def _require_projection_matches_artifacts(
    projection: _AuthenticatedReleaseSelectionDurableArtifactsV2,
    artifacts: _AuthenticatedArtifactsV2,
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
    expected = (
        artifacts.signed_envelope_bytes,
        artifacts.selector_input_bytes,
        artifacts.candidate_bytes,
        artifacts.signer_registry_bytes,
        artifacts.signature_envelopes_bytes,
        artifacts.quorum_report_bytes,
        artifacts.external_trust_pins_bytes,
        artifacts.authentication_evidence_bytes,
    )
    if observed != expected:
        raise ValueError("durable-store projection differs from revalidated evidence")


def _require_store_identity_matches_artifacts(
    identity: SpotV7AuthenticatedReleaseSelectionStoreIdentityV2,
    artifacts: _AuthenticatedArtifactsV2,
) -> None:
    envelope = artifacts.envelope
    candidate_document = cast(dict[str, Any], json.loads(artifacts.candidate_bytes))
    lineage = cast(dict[str, Any], candidate_document["lineage"])
    checks = (
        (envelope.application_id == identity.application_id, "APPLICATION_ID_MISMATCH"),
        (envelope.chain_id == identity.chain_id, "CHAIN_ID_MISMATCH"),
        (envelope.domain_id == identity.domain_id, "DOMAIN_ID_MISMATCH"),
        (envelope.release_profile == identity.release_profile, "RELEASE_PROFILE_MISMATCH"),
        (envelope.signer_registry_id == identity.signer_registry_id, "REGISTRY_ID_MISMATCH"),
        (
            envelope.signer_registry_hash == identity.expected_signer_registry_hash,
            "REGISTRY_HASH_MISMATCH",
        ),
        (
            envelope.signer_registry_revision == identity.expected_signer_registry_revision,
            "REGISTRY_REVISION_MISMATCH",
        ),
        (
            envelope.signer_registry_activation_epoch == identity.signer_registry_activation_epoch,
            "REGISTRY_ACTIVATION_MISMATCH",
        ),
        (
            envelope.signer_registry_revocation_epoch == identity.signer_registry_revocation_epoch,
            "REGISTRY_REVOCATION_MISMATCH",
        ),
        (
            envelope.quorum_threshold == identity.expected_quorum_threshold,
            "QUORUM_THRESHOLD_MISMATCH",
        ),
        (
            envelope.rollback_policy_root == identity.rollback_policy_root,
            "ROLLBACK_POLICY_MISMATCH",
        ),
        (
            envelope.revocation_policy_root == identity.revocation_policy_root,
            "REVOCATION_POLICY_MISMATCH",
        ),
        (
            envelope.revocation_registry_root == identity.revocation_registry_root,
            "REVOCATION_REGISTRY_MISMATCH",
        ),
        (
            bytes.fromhex(cast(str, lineage["rollback_policy_root"]))
            == identity.rollback_policy_root,
            "CANDIDATE_ROLLBACK_POLICY_MISMATCH",
        ),
        (
            bytes.fromhex(cast(str, lineage["revocation_policy_root"]))
            == identity.revocation_policy_root,
            "CANDIDATE_REVOCATION_POLICY_MISMATCH",
        ),
    )
    for accepted, code in checks:
        if not accepted:
            raise _SelectionRejectV2(code)


def _apply_forward_transition(
    cursor: SpotV7AuthenticatedReleaseSelectionCursorV2,
    artifacts: _AuthenticatedArtifactsV2,
) -> SpotV7AuthenticatedReleaseSelectionCursorV2:
    selector = artifacts.selector
    candidate = artifacts.candidate
    envelope = artifacts.envelope
    if (
        cursor.last_evaluation_epoch is not None
        and selector.evaluation_epoch < cursor.last_evaluation_epoch
    ):
        raise _SelectionRejectV2("EVALUATION_EPOCH_ROLLBACK_REJECTED")
    if selector.evaluation_epoch < artifacts.activation_epoch:
        raise _SelectionRejectV2("CANDIDATE_NOT_ACTIVE")
    if (
        artifacts.expiration_epoch is not None
        and selector.evaluation_epoch >= artifacts.expiration_epoch
    ):
        raise _SelectionRejectV2("CANDIDATE_EXPIRED")
    if selector.expected_database_revision != cursor.database_revision:
        raise _SelectionRejectV2("DATABASE_REVISION_CAS_MISMATCH")
    if selector.expected_current_candidate_id != cursor.current_candidate_id:
        raise _SelectionRejectV2("CURRENT_CANDIDATE_CAS_MISMATCH")
    if selector.expected_current_select_input_id != cursor.current_selector_input_id:
        raise _SelectionRejectV2("CURRENT_SELECTION_CAS_MISMATCH")
    if envelope.expected_database_revision != selector.expected_database_revision:
        raise _SelectionRejectV2("ENVELOPE_DATABASE_REVISION_MISMATCH")
    if envelope.expected_current_candidate_id != selector.expected_current_candidate_id:
        raise _SelectionRejectV2("ENVELOPE_CURRENT_CANDIDATE_MISMATCH")
    if envelope.expected_current_select_input_id != selector.expected_current_select_input_id:
        raise _SelectionRejectV2("ENVELOPE_CURRENT_SELECTION_MISMATCH")
    current_revision = cursor.current_release_revision
    if current_revision is None:
        if candidate.release_revision != 1 or artifacts.parent_candidate_id is not None:
            raise _SelectionRejectV2("GENESIS_LINEAGE_MISMATCH")
    else:
        if candidate.release_revision < current_revision:
            raise _SelectionRejectV2("RELEASE_ROLLBACK_REJECTED")
        if candidate.release_revision == current_revision:
            code = (
                "RELEASE_REPLAY_CONFLICT"
                if candidate.candidate_id == cursor.current_candidate_id
                else "RELEASE_FORK_REJECTED"
            )
            raise _SelectionRejectV2(code)
        if candidate.release_revision != current_revision + 1:
            raise _SelectionRejectV2("RELEASE_REVISION_GAP")
        if artifacts.parent_candidate_id != cursor.current_candidate_id:
            raise _SelectionRejectV2("RELEASE_FORK_REJECTED")
    next_revision = cursor.database_revision + 1
    if next_revision > MAX_AUTHENTICATED_SELECTION_EVENTS_V2:
        raise _SelectionRejectV2("EVENT_LIMIT_REACHED")
    next_root = _event_state_root(cursor.state_root, next_revision, artifacts)
    return SpotV7AuthenticatedReleaseSelectionCursorV2(
        database_revision=next_revision,
        state_root=next_root,
        last_evaluation_epoch=selector.evaluation_epoch,
        current_candidate_id=candidate.candidate_id,
        current_candidate_sha256=hashlib.sha256(candidate.canonical_bytes).digest(),
        current_release_revision=candidate.release_revision,
        current_selector_input_id=selector.input_id,
    )


def _insert_event(
    connection: sqlite3.Connection,
    previous: SpotV7AuthenticatedReleaseSelectionCursorV2,
    result: SpotV7AuthenticatedReleaseSelectionCursorV2,
    artifacts: _AuthenticatedArtifactsV2,
    identity: SpotV7AuthenticatedReleaseSelectionStoreIdentityV2,
) -> None:
    connection.execute(
        """
        INSERT INTO spot_v7_authenticated_release_selection_events_v2 (
            event_revision_be, selector_input_id, selector_input_bytes,
            candidate_id, candidate_sha256, candidate_bytes,
            release_revision_be, evaluation_epoch_be,
            signed_envelope_bytes, signed_envelope_sha256,
            signer_registry_bytes, signer_registry_sha256,
            signer_registry_hash, signer_registry_revision_be,
            signature_envelopes_bytes, signature_envelopes_sha256,
            quorum_report_bytes, quorum_report_sha256, quorum_report_hash,
            external_trust_pins_bytes, external_trust_pins_sha256,
            external_trust_pin_identity,
            authentication_evidence_bytes, authentication_evidence_sha256,
            previous_state_root, result_state_root,
            durable_authenticated_selection_recorded,
            revocation_authority, release_authority, runtime_authority,
            settlement_authority, production_authority
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 1, 0, 0, 0, 0, 0)
        """,
        (
            _u64be(result.database_revision),
            artifacts.selector.input_id,
            artifacts.selector_input_bytes,
            artifacts.candidate.candidate_id,
            hashlib.sha256(artifacts.candidate_bytes).digest(),
            artifacts.candidate_bytes,
            _u64be(artifacts.candidate.release_revision),
            _u64be(artifacts.selector.evaluation_epoch),
            artifacts.signed_envelope_bytes,
            artifacts.signed_envelope_sha256,
            artifacts.signer_registry_bytes,
            artifacts.signer_registry_sha256,
            bytes.fromhex(artifacts.envelope.signer_registry_hash[2:]),
            _u64be(artifacts.envelope.signer_registry_revision),
            artifacts.signature_envelopes_bytes,
            artifacts.signature_envelopes_sha256,
            artifacts.quorum_report_bytes,
            artifacts.quorum_report_sha256,
            artifacts.quorum_report_hash,
            artifacts.external_trust_pins_bytes,
            artifacts.external_trust_pins_sha256,
            identity.external_trust_pin_identity,
            artifacts.authentication_evidence_bytes,
            artifacts.authentication_evidence_sha256,
            previous.state_root,
            result.state_root,
        ),
    )


def _cas_meta(
    connection: sqlite3.Connection,
    previous: SpotV7AuthenticatedReleaseSelectionCursorV2,
    result: SpotV7AuthenticatedReleaseSelectionCursorV2,
) -> None:
    updated = connection.execute(
        """
        UPDATE spot_v7_authenticated_release_selection_meta_v2
        SET database_revision_be = ?, state_root = ?, event_count = ?,
            last_evaluation_epoch_be = ?, current_candidate_id = ?,
            current_candidate_sha256 = ?, current_release_revision_be = ?,
            current_selector_input_id = ?
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
            result.current_selector_input_id,
            _u64be(previous.database_revision),
            previous.state_root,
        ),
    )
    if updated.rowcount != 1:
        raise ValueError("authenticated selection metadata CAS failed")


def _resolve_exact_replay(
    row: sqlite3.Row,
    artifacts: _AuthenticatedArtifactsV2,
    cursor: SpotV7AuthenticatedReleaseSelectionCursorV2,
    identity: SpotV7AuthenticatedReleaseSelectionStoreIdentityV2,
) -> SpotV7AuthenticatedReleaseSelectionResultV2:
    observed = _event_artifact_values(row)
    expected = _artifact_storage_values(artifacts, identity)
    if observed != expected:
        raise ValueError("stored authenticated selector identity collision or evidence drift")
    return _result(
        AuthenticatedReleaseSelectionDispositionV2.IDEMPOTENT,
        "EXACT_AUTHENTICATED_REPLAY",
        artifacts.selector.input_id,
        cursor,
    )


def _validate_complete_history(
    connection: sqlite3.Connection,
    identity: SpotV7AuthenticatedReleaseSelectionStoreIdentityV2,
) -> SpotV7AuthenticatedReleaseSelectionCursorV2:
    _validate_database_integrity(connection)
    meta = _read_meta(connection)
    _validate_meta_identity(meta, identity)
    cursor = _genesis_cursor(identity)
    rows = _read_all_events(connection)
    if len(rows) > MAX_AUTHENTICATED_SELECTION_EVENTS_V2:
        raise ValueError("authenticated selection event count exceeds maximum")
    for revision, row in enumerate(rows, start=1):
        if bytes(row["event_revision_be"]) != _u64be(revision):
            raise ValueError("authenticated selection revisions are not contiguous")
        evidence_bytes = bytes(row["authentication_evidence_bytes"])
        artifacts = _revalidate_authentication_evidence(evidence_bytes)
        _require_store_identity_matches_artifacts(identity, artifacts)
        if _event_artifact_values(row) != _artifact_storage_values(artifacts, identity):
            raise ValueError("stored authenticated selection artifact binding mismatch")
        if bytes(row["previous_state_root"]) != cursor.state_root:
            raise ValueError("stored authenticated selection previous root mismatch")
        cursor = _apply_forward_transition(cursor, artifacts)
        if cursor.database_revision != revision:
            raise ValueError("replayed authenticated selection revision mismatch")
        if bytes(row["result_state_root"]) != cursor.state_root:
            raise ValueError("stored authenticated selection result root mismatch")
        expected_flags = (1, 0, 0, 0, 0, 0)
        observed_flags = (
            int(row["durable_authenticated_selection_recorded"]),
            int(row["revocation_authority"]),
            int(row["release_authority"]),
            int(row["runtime_authority"]),
            int(row["settlement_authority"]),
            int(row["production_authority"]),
        )
        if observed_flags != expected_flags:
            raise ValueError("stored authenticated selection authority flags mismatch")
    if int(meta["event_count"]) != len(rows):
        raise ValueError("authenticated selection metadata event count mismatch")
    if _cursor_storage_values(cursor) != _meta_cursor_values(meta):
        raise ValueError("authenticated selection metadata disagrees with replayed history")
    return cursor


def _event_artifact_values(row: sqlite3.Row) -> tuple[object, ...]:
    return (
        bytes(row["selector_input_id"]),
        bytes(row["selector_input_bytes"]),
        bytes(row["candidate_id"]),
        bytes(row["candidate_sha256"]),
        bytes(row["candidate_bytes"]),
        bytes(row["release_revision_be"]),
        bytes(row["evaluation_epoch_be"]),
        bytes(row["signed_envelope_bytes"]),
        bytes(row["signed_envelope_sha256"]),
        bytes(row["signer_registry_bytes"]),
        bytes(row["signer_registry_sha256"]),
        bytes(row["signer_registry_hash"]),
        bytes(row["signer_registry_revision_be"]),
        bytes(row["signature_envelopes_bytes"]),
        bytes(row["signature_envelopes_sha256"]),
        bytes(row["quorum_report_bytes"]),
        bytes(row["quorum_report_sha256"]),
        bytes(row["quorum_report_hash"]),
        bytes(row["external_trust_pins_bytes"]),
        bytes(row["external_trust_pins_sha256"]),
        bytes(row["external_trust_pin_identity"]),
        bytes(row["authentication_evidence_bytes"]),
        bytes(row["authentication_evidence_sha256"]),
    )


def _artifact_storage_values(
    artifacts: _AuthenticatedArtifactsV2,
    identity: SpotV7AuthenticatedReleaseSelectionStoreIdentityV2,
) -> tuple[object, ...]:
    return (
        artifacts.selector.input_id,
        artifacts.selector_input_bytes,
        artifacts.candidate.candidate_id,
        hashlib.sha256(artifacts.candidate_bytes).digest(),
        artifacts.candidate_bytes,
        _u64be(artifacts.candidate.release_revision),
        _u64be(artifacts.selector.evaluation_epoch),
        artifacts.signed_envelope_bytes,
        artifacts.signed_envelope_sha256,
        artifacts.signer_registry_bytes,
        artifacts.signer_registry_sha256,
        bytes.fromhex(artifacts.envelope.signer_registry_hash[2:]),
        _u64be(artifacts.envelope.signer_registry_revision),
        artifacts.signature_envelopes_bytes,
        artifacts.signature_envelopes_sha256,
        artifacts.quorum_report_bytes,
        artifacts.quorum_report_sha256,
        artifacts.quorum_report_hash,
        artifacts.external_trust_pins_bytes,
        artifacts.external_trust_pins_sha256,
        identity.external_trust_pin_identity,
        artifacts.authentication_evidence_bytes,
        artifacts.authentication_evidence_sha256,
    )


def _initialize_or_validate(
    connection: sqlite3.Connection,
    identity: SpotV7AuthenticatedReleaseSelectionStoreIdentityV2,
) -> None:
    if not connection.in_transaction:
        raise ValueError("authenticated selection initialization requires a transaction")
    existing = connection.execute(
        "SELECT name FROM sqlite_master WHERE name NOT LIKE 'sqlite_%'"
    ).fetchall()
    if not existing:
        if int(connection.execute("PRAGMA application_id").fetchone()[0]) != 0:
            raise ValueError("empty authenticated selection database has an application_id")
        if int(connection.execute("PRAGMA user_version").fetchone()[0]) != 0:
            raise ValueError("empty authenticated selection database has a user_version")
        connection.execute(f"PRAGMA application_id = {STORE_APPLICATION_ID_V2}")
        connection.execute(f"PRAGMA user_version = {STORE_SCHEMA_VERSION_V2}")
        for statement in _SCHEMA_STATEMENTS_V2:
            connection.execute(statement)
        genesis = _genesis_cursor(identity)
        connection.execute(
            """
            INSERT INTO spot_v7_authenticated_release_selection_meta_v2 (
                singleton, schema_version, store_identity_bytes,
                store_identity_sha256, external_trust_pin_identity,
                expected_signer_registry_hash,
                expected_signer_registry_revision_be, rollback_policy_root,
                revocation_policy_root, revocation_registry_root,
                database_revision_be, state_root, event_count,
                last_evaluation_epoch_be, current_candidate_id,
                current_candidate_sha256, current_release_revision_be,
                current_selector_input_id, release_authority, runtime_authority,
                settlement_authority, production_authority
            ) VALUES (1, 2, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 0, NULL, NULL, NULL, NULL, NULL, 0, 0, 0, 0)
            """,
            (
                identity.canonical_bytes,
                identity.identity_sha256,
                identity.external_trust_pin_identity,
                bytes.fromhex(identity.expected_signer_registry_hash[2:]),
                _u64be(identity.expected_signer_registry_revision),
                identity.rollback_policy_root,
                identity.revocation_policy_root,
                identity.revocation_registry_root,
                _u64be(0),
                genesis.state_root,
            ),
        )
    _validate_schema(connection)
    _validate_complete_history(connection, identity)


def _validate_schema(connection: sqlite3.Connection) -> None:
    if int(connection.execute("PRAGMA application_id").fetchone()[0]) != STORE_APPLICATION_ID_V2:
        raise ValueError("authenticated selection application_id mismatch")
    if int(connection.execute("PRAGMA user_version").fetchone()[0]) != STORE_SCHEMA_VERSION_V2:
        raise ValueError("authenticated selection user_version mismatch")
    rows = connection.execute(
        """
        SELECT type, name, sql FROM sqlite_master
        WHERE name NOT LIKE 'sqlite_%'
        ORDER BY type, name
        """
    ).fetchall()
    observed = {(str(row["type"]), str(row["name"])) for row in rows}
    expected = {("table", name) for name in _EXPECTED_SCHEMA_SQL_V2}
    if observed != expected:
        raise ValueError("authenticated selection schema object set mismatch")
    for row in rows:
        name = str(row["name"])
        if _normalize_sql(str(row["sql"])) != _normalize_sql(_EXPECTED_SCHEMA_SQL_V2[name]):
            raise ValueError(f"authenticated selection schema SQL mismatch for {name}")


def _validate_meta_identity(
    row: sqlite3.Row,
    identity: SpotV7AuthenticatedReleaseSelectionStoreIdentityV2,
) -> None:
    observed = (
        bytes(row["store_identity_bytes"]),
        bytes(row["store_identity_sha256"]),
        bytes(row["external_trust_pin_identity"]),
        bytes(row["expected_signer_registry_hash"]),
        bytes(row["expected_signer_registry_revision_be"]),
        bytes(row["rollback_policy_root"]),
        bytes(row["revocation_policy_root"]),
        bytes(row["revocation_registry_root"]),
        int(row["release_authority"]),
        int(row["runtime_authority"]),
        int(row["settlement_authority"]),
        int(row["production_authority"]),
    )
    expected = (
        identity.canonical_bytes,
        identity.identity_sha256,
        identity.external_trust_pin_identity,
        bytes.fromhex(identity.expected_signer_registry_hash[2:]),
        _u64be(identity.expected_signer_registry_revision),
        identity.rollback_policy_root,
        identity.revocation_policy_root,
        identity.revocation_registry_root,
        0,
        0,
        0,
        0,
    )
    if observed != expected:
        raise ValueError("authenticated selection store identity drift")


def _validate_database_integrity(connection: sqlite3.Connection) -> None:
    quick = connection.execute("PRAGMA quick_check").fetchall()
    if len(quick) != 1 or quick[0][0] != "ok":
        raise ValueError("authenticated selection quick_check failed")
    if connection.execute("PRAGMA foreign_key_check").fetchone() is not None:
        raise ValueError("authenticated selection foreign_key_check failed")


def _read_meta(connection: sqlite3.Connection) -> sqlite3.Row:
    row = connection.execute(
        "SELECT * FROM spot_v7_authenticated_release_selection_meta_v2 WHERE singleton = 1"
    ).fetchone()
    if row is None:
        raise ValueError("authenticated selection metadata row missing")
    return row


def _read_all_events(connection: sqlite3.Connection) -> list[sqlite3.Row]:
    return connection.execute(
        "SELECT * FROM spot_v7_authenticated_release_selection_events_v2 ORDER BY event_revision_be"
    ).fetchall()


def _read_event_by_selector_id(
    connection: sqlite3.Connection,
    selector_input_id: bytes,
) -> sqlite3.Row | None:
    return connection.execute(
        "SELECT * FROM spot_v7_authenticated_release_selection_events_v2 WHERE selector_input_id = ?",
        (selector_input_id,),
    ).fetchone()


def _genesis_cursor(
    identity: SpotV7AuthenticatedReleaseSelectionStoreIdentityV2,
) -> SpotV7AuthenticatedReleaseSelectionCursorV2:
    root = _domain_hash(
        _GENESIS_STATE_DOMAIN_V2,
        STORE_SCHEMA_VERSION_V2.to_bytes(4, "big")
        + identity.identity_sha256
        + identity.external_trust_pin_identity,
    )
    return SpotV7AuthenticatedReleaseSelectionCursorV2(
        database_revision=0,
        state_root=root,
        last_evaluation_epoch=None,
        current_candidate_id=None,
        current_candidate_sha256=None,
        current_release_revision=None,
        current_selector_input_id=None,
    )


def _event_state_root(
    previous: bytes,
    revision: int,
    artifacts: _AuthenticatedArtifactsV2,
) -> bytes:
    payload = (
        previous
        + _u64be(revision)
        + artifacts.selector.input_id
        + artifacts.candidate.candidate_id
        + hashlib.sha256(artifacts.candidate_bytes).digest()
        + artifacts.signed_envelope_sha256
        + artifacts.signer_registry_sha256
        + artifacts.signature_envelopes_sha256
        + artifacts.quorum_report_sha256
        + artifacts.external_trust_pins_sha256
        + artifacts.authentication_evidence_sha256
    )
    return _domain_hash(_EVENT_STATE_DOMAIN_V2, payload)


def _cursor_storage_values(
    cursor: SpotV7AuthenticatedReleaseSelectionCursorV2,
) -> tuple[object, ...]:
    return (
        _u64be(cursor.database_revision),
        cursor.state_root,
        cursor.database_revision,
        _optional_u64be(cursor.last_evaluation_epoch),
        cursor.current_candidate_id,
        cursor.current_candidate_sha256,
        _optional_u64be(cursor.current_release_revision),
        cursor.current_selector_input_id,
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
        _optional_blob(row["current_selector_input_id"]),
    )


def _result(
    disposition: AuthenticatedReleaseSelectionDispositionV2,
    code: str,
    selector_input_id: bytes | None,
    cursor: SpotV7AuthenticatedReleaseSelectionCursorV2,
) -> SpotV7AuthenticatedReleaseSelectionResultV2:
    return SpotV7AuthenticatedReleaseSelectionResultV2._from_store(
        disposition=disposition,
        code=code,
        selector_input_id=selector_input_id,
        cursor=cursor,
        seal=_AUTHENTICATED_RELEASE_SELECTION_RESULT_SEAL_V2,
    )


def _decode_exact_evidence_document(raw: bytes) -> dict[str, object]:
    if type(raw) is not bytes or not raw or len(raw) > MAX_AUTHENTICATION_EVIDENCE_BYTES_V2:
        raise ValueError("authentication evidence is empty, non-bytes, or oversized")
    _require_bounded_json_depth(raw)
    try:
        text = raw.decode("ascii")
        value = json.loads(
            text,
            object_pairs_hook=_reject_duplicate_keys,
            parse_float=_reject_float,
            parse_constant=_reject_nonfinite,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise ValueError("authentication evidence is invalid canonical JSON") from exc
    document = _require_exact_fields(value, expected=_EVIDENCE_FIELDS_V1, name="evidence")
    if document["schema"] != SPOT_V7_RELEASE_SELECTION_AUTHENTICATION_EVIDENCE_SCHEMA_V1:
        raise ValueError("authentication evidence schema mismatch")
    if canonical_json_bytes(document) != raw:
        raise ValueError("authentication evidence bytes are noncanonical")
    return document


def _pins_from_document(
    document: Mapping[str, object],
) -> SpotV7ReleaseSelectionExternalTrustPinsV1:
    return SpotV7ReleaseSelectionExternalTrustPinsV1(
        application_id=_require_token(document["application_id"], name="application_id"),
        chain_id=_require_token(document["chain_id"], name="chain_id"),
        domain_id=_require_token(document["domain_id"], name="domain_id"),
        release_profile=_require_token(document["release_profile"], name="release_profile"),
        trusted_evaluation_epoch=_require_u64(
            document["trusted_evaluation_epoch"], name="trusted_evaluation_epoch"
        ),
        expected_database_revision=_require_u64(
            document["expected_database_revision"], name="expected_database_revision"
        ),
        expected_current_candidate_id=_decode_optional_root_bytes(
            document["expected_current_candidate_id"], name="expected_current_candidate_id"
        ),
        expected_current_select_input_id=_decode_optional_root_bytes(
            document["expected_current_select_input_id"],
            name="expected_current_select_input_id",
        ),
        minimum_target_release_revision=_require_positive_u64(
            document["minimum_target_release_revision"],
            name="minimum_target_release_revision",
        ),
        rollback_policy_root=_decode_root_bytes(
            document["rollback_policy_root"], name="rollback_policy_root"
        ),
        revocation_policy_root=_decode_root_bytes(
            document["revocation_policy_root"], name="revocation_policy_root"
        ),
        revocation_registry_root=_decode_root_bytes(
            document["revocation_registry_root"], name="revocation_registry_root"
        ),
        signer_registry_id=_require_token(
            document["signer_registry_id"], name="signer_registry_id"
        ),
        expected_signer_registry_hash=_require_root(
            document["expected_signer_registry_hash"], name="expected_signer_registry_hash"
        ),
        signer_registry_revision=_require_positive_u64(
            document["signer_registry_revision"], name="signer_registry_revision"
        ),
        signer_registry_activation_epoch=_require_u64(
            document["signer_registry_activation_epoch"],
            name="signer_registry_activation_epoch",
        ),
        signer_registry_revocation_epoch=_require_optional_u64(
            document["signer_registry_revocation_epoch"],
            name="signer_registry_revocation_epoch",
        ),
        expected_quorum_threshold=_require_positive_u64(
            document["expected_quorum_threshold"], name="expected_quorum_threshold"
        ),
    )


def _require_exact_fields(
    value: object,
    *,
    expected: frozenset[str],
    name: str,
) -> dict[str, object]:
    if type(value) is not dict:
        raise ValueError(f"{name} must be an exact object")
    output = cast(dict[str, object], value)
    keys = frozenset(output)
    if keys != expected:
        raise ValueError(f"{name} exact field set mismatch")
    return output


def _require_exact_dict(value: object, *, name: str) -> dict[str, Any]:
    if type(value) is not dict:
        raise ValueError(f"{name} must be an exact object")
    return cast(dict[str, Any], value)


def _require_exact_dict_sequence(value: object, *, name: str) -> tuple[dict[str, Any], ...]:
    if type(value) is not list:
        raise ValueError(f"{name} must be an exact list")
    output: list[dict[str, Any]] = []
    for index, item in enumerate(cast(Sequence[object], value)):
        if type(item) is not dict:
            raise ValueError(f"{name}[{index}] must be an exact object")
        output.append(cast(dict[str, Any], item))
    if not output:
        raise ValueError(f"{name} cannot be empty")
    if output != sorted(output, key=canonical_json_bytes):
        raise ValueError(f"{name} must be canonically ordered")
    return tuple(output)


def _decode_hex_bytes(
    value: object,
    *,
    name: str,
    exact_bytes: int | None = None,
    minimum_bytes: int | None = None,
    maximum_bytes: int | None = None,
) -> bytes:
    if type(value) is not str or not value or len(value) % 2 != 0:
        raise ValueError(f"{name} must be canonical lowercase hex")
    if value != value.lower() or any(character not in "0123456789abcdef" for character in value):
        raise ValueError(f"{name} must be canonical lowercase hex")
    raw = bytes.fromhex(value)
    if exact_bytes is not None and len(raw) != exact_bytes:
        raise ValueError(f"{name} length mismatch")
    if minimum_bytes is not None and len(raw) < minimum_bytes:
        raise ValueError(f"{name} is too short")
    if maximum_bytes is not None and len(raw) > maximum_bytes:
        raise ValueError(f"{name} is too large")
    return raw


def _decode_root_bytes(value: object, *, name: str) -> bytes:
    root = _require_root(value, name=name)
    return bytes.fromhex(root[2:])


def _decode_optional_root_bytes(value: object, *, name: str) -> bytes | None:
    if value is None:
        return None
    return _decode_root_bytes(value, name=name)


def _require_bounded_json_depth(raw: bytes) -> None:
    depth = 0
    in_string = False
    escaped = False
    for byte in raw:
        if in_string:
            if escaped:
                escaped = False
            elif byte == 0x5C:
                escaped = True
            elif byte == 0x22:
                in_string = False
            continue
        if byte == 0x22:
            in_string = True
        elif byte in {0x5B, 0x7B}:
            depth += 1
            if depth > MAX_JSON_DEPTH_V2:
                raise ValueError("authentication evidence is too deeply nested")
        elif byte in {0x5D, 0x7D}:
            depth -= 1
            if depth < 0:
                raise ValueError("authentication evidence framing is invalid")
    if depth != 0 or in_string or escaped:
        raise ValueError("authentication evidence framing is invalid")


def _reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    output: dict[str, object] = {}
    for key, value in pairs:
        if key in output:
            raise ValueError(f"duplicate JSON key: {key}")
        output[key] = value
    return output


def _reject_float(_value: str) -> NoReturn:
    raise ValueError("floating-point JSON values are forbidden")


def _reject_nonfinite(_value: str) -> NoReturn:
    raise ValueError("non-finite JSON values are forbidden")


def _require_maximum_size(raw: bytes, *, maximum: int, name: str) -> None:
    if not raw or len(raw) > maximum:
        raise ValueError(f"{name} is empty or oversized")


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
    if type(value) is not int or not 0 <= value <= MAX_U64_V2:
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


def _domain_hash(domain: bytes, payload: bytes) -> bytes:
    return hashlib.sha256(
        len(domain).to_bytes(2, "big") + domain + len(payload).to_bytes(8, "big") + payload
    ).digest()


def _connect_database(path: Path, busy_timeout_ms: int) -> sqlite3.Connection:
    timeout_seconds = max(1, (busy_timeout_ms + 999) // 1_000)
    connection = sqlite3.connect(path, timeout=timeout_seconds, isolation_level=None)
    try:
        connection.row_factory = sqlite3.Row
        connection.execute("PRAGMA foreign_keys = ON")
        mode = str(connection.execute("PRAGMA journal_mode = DELETE").fetchone()[0]).lower()
        if mode != "delete":
            raise ValueError("authenticated selection journal_mode must be DELETE")
        connection.execute("PRAGMA synchronous = EXTRA")
        connection.execute(f"PRAGMA busy_timeout = {busy_timeout_ms}")
        connection.execute("PRAGMA trusted_schema = OFF")
        connection.execute("PRAGMA temp_store = MEMORY")
        if int(connection.execute("PRAGMA foreign_keys").fetchone()[0]) != 1:
            raise ValueError("authenticated selection foreign_keys must be enabled")
        if int(connection.execute("PRAGMA synchronous").fetchone()[0]) != 3:
            raise ValueError("authenticated selection synchronous must be EXTRA")
        if int(connection.execute("PRAGMA trusted_schema").fetchone()[0]) != 0:
            raise ValueError("authenticated selection trusted_schema must be disabled")
        if int(connection.execute("PRAGMA busy_timeout").fetchone()[0]) != busy_timeout_ms:
            raise ValueError("authenticated selection busy_timeout mismatch")
    except (sqlite3.Error, ValueError):
        connection.close()
        raise
    return connection


def _validate_store_path(path: Path, busy_timeout_ms: int) -> None:
    if not isinstance(path, Path):
        raise TypeError("authenticated selection path must be pathlib.Path")
    if not path.is_absolute():
        raise ValueError("authenticated selection path must be absolute")
    if path.resolve(strict=False) != path:
        raise ValueError("authenticated selection path must be canonical and symlink-free")
    if type(busy_timeout_ms) is not int or not 1 <= busy_timeout_ms <= MAX_BUSY_TIMEOUT_MS_V2:
        raise ValueError("authenticated selection busy_timeout_ms is out of range")
    parent = path.parent
    parent_stat = parent.stat(follow_symlinks=False)
    if not stat.S_ISDIR(parent_stat.st_mode):
        raise ValueError("authenticated selection parent is not a directory")
    if parent_stat.st_uid != os.getuid() or stat.S_IMODE(parent_stat.st_mode) & 0o077:
        raise ValueError("authenticated selection parent must be private and owned by this uid")


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
        raise ValueError("authenticated selection database is not a regular file")
    if file_stat.st_uid != os.getuid() or stat.S_IMODE(file_stat.st_mode) != 0o600:
        raise ValueError("authenticated selection database must be private and owned by this uid")
    if file_stat.st_nlink != 1:
        raise ValueError("authenticated selection database must have exactly one hard link")


def _fsync_directory(path: Path) -> None:
    descriptor = os.open(
        path,
        os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_CLOEXEC", 0),
    )
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _normalize_sql(value: str) -> str:
    return " ".join(value.strip().removesuffix(";").split())


__all__ = [
    "AuthenticatedReleaseSelectionDispositionV2",
    "SQLiteSpotV7AuthenticatedReleaseSelectionStoreV2",
    "SpotV7AuthenticatedReleaseSelectionCursorV2",
    "SpotV7AuthenticatedReleaseSelectionDurabilityUncertainV2",
    "SpotV7AuthenticatedReleaseSelectionResultV2",
    "SpotV7AuthenticatedReleaseSelectionStoreErrorV2",
    "SpotV7AuthenticatedReleaseSelectionStoreIdentityV2",
    "SPOT_V7_AUTHENTICATED_RELEASE_SELECTION_MONOTONIC_ANCHOR_BLOCKER_V2",
    "SPOT_V7_AUTHENTICATED_RELEASE_SELECTION_REVOCATION_BLOCKER_V2",
    "SPOT_V7_AUTHENTICATED_RELEASE_SELECTION_SAME_UID_BLOCKER_V2",
]
