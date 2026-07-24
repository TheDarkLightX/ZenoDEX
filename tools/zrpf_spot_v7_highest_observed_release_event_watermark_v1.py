"""Authority-neutral currentness checks against an external watermark projection.

The raw watermark document is untrusted.  This module proves only canonical
binding and a deterministic relation among exact checkpoint bytes.  A future
protocol adapter must authenticate the watermark in an externally monotonic
system before any later boundary may consider release currentness established.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from enum import Enum
from typing import Final, NoReturn, SupportsIndex, final

from src.state.canonical import canonical_json_bytes, domain_sep_bytes, encode_bytes
from tools import zrpf_spot_v7_release_state_checkpoint_v1 as checkpoint

HIGHEST_OBSERVED_RELEASE_EVENT_WATERMARK_SCHEMA_V1: Final = (
    "zenodex.zrpf.spot_v7.highest_observed_release_event_watermark.v1"
)
AUTHORITY_NEUTRAL_RELEASE_CURRENTNESS_ASSESSMENT_SCHEMA_V1: Final = (
    "zenodex.zrpf.spot_v7.authority_neutral_release_currentness_assessment.v1"
)
MAX_HIGHEST_OBSERVED_WATERMARK_BYTES_V1: Final = 16 * 1_024
MAX_HIGHEST_OBSERVED_WATERMARK_DEPTH_V1: Final = 2
MAX_U64_V1: Final = (1 << 64) - 1
ZERO_DIGEST_HEX_V1: Final = "00" * 32

_WATERMARK_HASH_DOMAIN_V1: Final = domain_sep_bytes(
    "zrpf_spot_v7_highest_observed_release_event_watermark",
    version=1,
)
_ASSESSMENT_HASH_DOMAIN_V1: Final = domain_sep_bytes(
    "zrpf_spot_v7_authority_neutral_release_currentness_assessment",
    version=1,
)
_DIGEST_RE: Final = re.compile(r"^[0-9a-f]{64}$")
_TOKEN_RE: Final = re.compile(r"^[A-Za-z0-9._:-]{1,128}$")
_WATERMARK_FIELDS_V1: Final = frozenset(
    {
        "application_id",
        "chain_id",
        "domain_id",
        "external_backend_commitment",
        "external_backend_id",
        "external_parent_commitment",
        "external_position",
        "highest_observed_checkpoint_hash",
        "highest_observed_database_revision",
        "highest_observed_event_kind",
        "highest_observed_release_state_root",
        "highest_observed_revocation_record_id",
        "highest_observed_select_input_id",
        "latest_finalized_checkpoint_hash",
        "latest_finalized_database_revision",
        "release_profile",
        "schema",
        "store_identity_hash",
        "watermark_hash",
    }
)


class SpotV7HighestObservedReleaseEventWatermarkRejectV1(ValueError):
    """Stable fail-closed rejection at the raw watermark boundary."""

    def __init__(self, code: str, detail: str) -> None:
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}")


def _reject(
    code: str,
    detail: str,
) -> SpotV7HighestObservedReleaseEventWatermarkRejectV1:
    return SpotV7HighestObservedReleaseEventWatermarkRejectV1(code, detail)


class ObservedReleaseEventKindV1(str, Enum):
    GENESIS = "GENESIS"
    SELECT = "SELECT"
    REVOKE = "REVOKE"


class ReleaseCurrentnessDispositionV1(str, Enum):
    PAUSED = "PAUSED"


class ReleaseCurrentnessRelationV1(str, Enum):
    LOCAL_BEHIND_FINALIZED = "LOCAL_BEHIND_FINALIZED"
    LOCAL_FORK_AT_FINALIZED = "LOCAL_FORK_AT_FINALIZED"
    LOCAL_MATCHES_FINALIZED_BEHIND_PENDING_SELECTION = (
        "LOCAL_MATCHES_FINALIZED_BEHIND_PENDING_SELECTION"
    )
    LOCAL_MATCHES_FINALIZED_BEHIND_PENDING_REVOCATION = (
        "LOCAL_MATCHES_FINALIZED_BEHIND_PENDING_REVOCATION"
    )
    LOCAL_FORK_AT_HIGHEST_OBSERVED = "LOCAL_FORK_AT_HIGHEST_OBSERVED"
    LOCAL_AHEAD_OF_HIGHEST_OBSERVED = "LOCAL_AHEAD_OF_HIGHEST_OBSERVED"
    LOCAL_MATCHES_GENESIS = "LOCAL_MATCHES_GENESIS"
    LOCAL_MATCHES_FINALIZED_SELECTION = "LOCAL_MATCHES_FINALIZED_SELECTION"
    LOCAL_MATCHES_PENDING_SELECTION = "LOCAL_MATCHES_PENDING_SELECTION"
    LOCAL_MATCHES_REVOKED_HIGHEST_OBSERVED = "LOCAL_MATCHES_REVOKED_HIGHEST_OBSERVED"


class _AuthorityNeutralClaimsV1:
    @property
    def external_finality_authenticated(self) -> bool:
        return False

    @property
    def store_derived_checkpoint_provenance_verified(self) -> bool:
        return False

    @property
    def external_monotonicity_authenticated(self) -> bool:
        return False

    @property
    def rollback_safe_currentness_established(self) -> bool:
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


@final
@dataclass(frozen=True, slots=True)
class SpotV7HighestObservedReleaseEventWatermarkV1(_AuthorityNeutralClaimsV1):
    """Canonical untrusted projection carrying no external authority."""

    canonical_bytes: bytes
    application_id: str
    chain_id: str
    domain_id: str
    release_profile: str
    store_identity_hash: str
    external_backend_id: str
    external_position: int
    external_backend_commitment: str
    external_parent_commitment: str
    latest_finalized_checkpoint_hash: str
    latest_finalized_database_revision: int
    highest_observed_checkpoint_hash: str
    highest_observed_database_revision: int
    highest_observed_release_state_root: str
    highest_observed_event_kind: ObservedReleaseEventKindV1
    highest_observed_select_input_id: str | None
    highest_observed_revocation_record_id: str | None
    watermark_hash: str


def build_spot_v7_highest_observed_release_event_watermark_v1(
    *,
    application_id: str,
    chain_id: str,
    domain_id: str,
    release_profile: str,
    store_identity_hash: str,
    external_backend_id: str,
    external_position: int,
    external_backend_commitment: str,
    external_parent_commitment: str,
    latest_finalized_checkpoint_hash: str,
    latest_finalized_database_revision: int,
    highest_observed_checkpoint_hash: str,
    highest_observed_database_revision: int,
    highest_observed_release_state_root: str,
    highest_observed_event_kind: ObservedReleaseEventKindV1,
    highest_observed_select_input_id: str | None,
    highest_observed_revocation_record_id: str | None,
) -> bytes:
    """Build canonical raw projection bytes without authenticating the backend."""

    event_kind = _require_event_kind_input(highest_observed_event_kind)
    body: dict[str, object] = {
        "application_id": _require_token(application_id, name="application_id"),
        "chain_id": _require_token(chain_id, name="chain_id"),
        "domain_id": _require_token(domain_id, name="domain_id"),
        "external_backend_commitment": _require_digest(
            external_backend_commitment,
            name="external_backend_commitment",
        ),
        "external_backend_id": _require_token(
            external_backend_id,
            name="external_backend_id",
        ),
        "external_parent_commitment": _require_digest_allow_zero(
            external_parent_commitment,
            name="external_parent_commitment",
        ),
        "external_position": _require_u64(external_position, name="external_position"),
        "highest_observed_checkpoint_hash": _require_digest(
            highest_observed_checkpoint_hash,
            name="highest_observed_checkpoint_hash",
        ),
        "highest_observed_database_revision": _require_u64(
            highest_observed_database_revision,
            name="highest_observed_database_revision",
        ),
        "highest_observed_event_kind": event_kind.value,
        "highest_observed_release_state_root": _require_digest(
            highest_observed_release_state_root,
            name="highest_observed_release_state_root",
        ),
        "highest_observed_revocation_record_id": _require_optional_digest(
            highest_observed_revocation_record_id,
            name="highest_observed_revocation_record_id",
        ),
        "highest_observed_select_input_id": _require_optional_digest(
            highest_observed_select_input_id,
            name="highest_observed_select_input_id",
        ),
        "latest_finalized_checkpoint_hash": _require_digest(
            latest_finalized_checkpoint_hash,
            name="latest_finalized_checkpoint_hash",
        ),
        "latest_finalized_database_revision": _require_u64(
            latest_finalized_database_revision,
            name="latest_finalized_database_revision",
        ),
        "release_profile": _require_token(release_profile, name="release_profile"),
        "schema": HIGHEST_OBSERVED_RELEASE_EVENT_WATERMARK_SCHEMA_V1,
        "store_identity_hash": _require_digest(
            store_identity_hash,
            name="store_identity_hash",
        ),
    }
    _validate_watermark_shape(body)
    document = dict(body)
    document["watermark_hash"] = _watermark_hash(body)
    raw = canonical_json_bytes(document) + b"\n"
    if len(raw) > MAX_HIGHEST_OBSERVED_WATERMARK_BYTES_V1:
        raise _reject("WATERMARK_SIZE", "highest-observed watermark is oversized")
    return raw


def parse_exact_spot_v7_highest_observed_release_event_watermark_v1(
    raw: bytes,
) -> SpotV7HighestObservedReleaseEventWatermarkV1:
    """Parse exact canonical raw projection bytes and rederive their self-hash."""

    document = _decode_exact_watermark(raw)
    body = {key: value for key, value in document.items() if key != "watermark_hash"}
    event_kind = _validate_watermark_shape(body)
    expected_hash = _watermark_hash(body)
    actual_hash = _require_digest(document["watermark_hash"], name="watermark_hash")
    if actual_hash != expected_hash:
        raise _reject("WATERMARK_HASH_MISMATCH", "watermark hash does not match bytes")
    return SpotV7HighestObservedReleaseEventWatermarkV1(
        canonical_bytes=raw,
        application_id=_require_token(document["application_id"], name="application_id"),
        chain_id=_require_token(document["chain_id"], name="chain_id"),
        domain_id=_require_token(document["domain_id"], name="domain_id"),
        release_profile=_require_token(document["release_profile"], name="release_profile"),
        store_identity_hash=_require_digest(
            document["store_identity_hash"],
            name="store_identity_hash",
        ),
        external_backend_id=_require_token(
            document["external_backend_id"],
            name="external_backend_id",
        ),
        external_position=_require_u64(
            document["external_position"],
            name="external_position",
        ),
        external_backend_commitment=_require_digest(
            document["external_backend_commitment"],
            name="external_backend_commitment",
        ),
        external_parent_commitment=_require_digest_allow_zero(
            document["external_parent_commitment"],
            name="external_parent_commitment",
        ),
        latest_finalized_checkpoint_hash=_require_digest(
            document["latest_finalized_checkpoint_hash"],
            name="latest_finalized_checkpoint_hash",
        ),
        latest_finalized_database_revision=_require_u64(
            document["latest_finalized_database_revision"],
            name="latest_finalized_database_revision",
        ),
        highest_observed_checkpoint_hash=_require_digest(
            document["highest_observed_checkpoint_hash"],
            name="highest_observed_checkpoint_hash",
        ),
        highest_observed_database_revision=_require_u64(
            document["highest_observed_database_revision"],
            name="highest_observed_database_revision",
        ),
        highest_observed_release_state_root=_require_digest(
            document["highest_observed_release_state_root"],
            name="highest_observed_release_state_root",
        ),
        highest_observed_event_kind=event_kind,
        highest_observed_select_input_id=_require_optional_digest(
            document["highest_observed_select_input_id"],
            name="highest_observed_select_input_id",
        ),
        highest_observed_revocation_record_id=_require_optional_digest(
            document["highest_observed_revocation_record_id"],
            name="highest_observed_revocation_record_id",
        ),
        watermark_hash=actual_hash,
    )


class _ReleaseCurrentnessAssessmentSealV1:
    __slots__ = ()


_RELEASE_CURRENTNESS_ASSESSMENT_SEAL_V1: Final = _ReleaseCurrentnessAssessmentSealV1()


@final
class _AuthorityNeutralReleaseCurrentnessAssessmentV1(_AuthorityNeutralClaimsV1):
    """Opaque deterministic assessment that can only pause operation."""

    __slots__ = (
        "_assessment_sha256",
        "_blocker_code",
        "_canonical_assessment_bytes",
        "_exact_finalized_checkpoint_bytes",
        "_exact_highest_observed_checkpoint_bytes",
        "_exact_local_checkpoint_bytes",
        "_exact_watermark_bytes",
        "_highest_observed_database_revision",
        "_local_database_revision",
        "_relation",
    )
    _assessment_sha256: bytes
    _blocker_code: str
    _canonical_assessment_bytes: bytes
    _exact_finalized_checkpoint_bytes: bytes
    _exact_highest_observed_checkpoint_bytes: bytes
    _exact_local_checkpoint_bytes: bytes
    _exact_watermark_bytes: bytes
    _highest_observed_database_revision: int
    _local_database_revision: int
    _relation: ReleaseCurrentnessRelationV1

    def __new__(cls) -> _AuthorityNeutralReleaseCurrentnessAssessmentV1:
        raise TypeError("release-currentness assessment requires checked construction")

    @classmethod
    def _from_checked(
        cls,
        *,
        exact_local_checkpoint_bytes: bytes,
        exact_finalized_checkpoint_bytes: bytes,
        exact_highest_observed_checkpoint_bytes: bytes,
        exact_watermark_bytes: bytes,
        relation: ReleaseCurrentnessRelationV1,
        blocker_code: str,
        local_database_revision: int,
        highest_observed_database_revision: int,
        local_checkpoint: checkpoint.SpotV7ReleaseStateCheckpointV1,
        finalized_checkpoint: checkpoint.SpotV7ReleaseStateCheckpointV1,
        highest_observed_checkpoint: checkpoint.SpotV7ReleaseStateCheckpointV1,
        watermark_value: SpotV7HighestObservedReleaseEventWatermarkV1,
        seal: _ReleaseCurrentnessAssessmentSealV1,
    ) -> _AuthorityNeutralReleaseCurrentnessAssessmentV1:
        if seal is not _RELEASE_CURRENTNESS_ASSESSMENT_SEAL_V1:
            raise TypeError("release-currentness assessment requires the module-private seal")
        exact_inputs = _require_exact_input_bytes(
            exact_local_checkpoint_bytes=exact_local_checkpoint_bytes,
            exact_finalized_checkpoint_bytes=exact_finalized_checkpoint_bytes,
            exact_highest_observed_checkpoint_bytes=exact_highest_observed_checkpoint_bytes,
            exact_watermark_bytes=exact_watermark_bytes,
        )
        if type(relation) is not ReleaseCurrentnessRelationV1:
            raise TypeError("relation must be the exact V1 enum")
        blocker = _require_token(blocker_code, name="blocker_code")
        local_revision = _require_u64(
            local_database_revision,
            name="local_database_revision",
        )
        observed_revision = _require_u64(
            highest_observed_database_revision,
            name="highest_observed_database_revision",
        )
        canonical = _canonical_assessment_bytes(
            exact_inputs=exact_inputs,
            relation=relation,
            blocker_code=blocker,
            local_checkpoint=local_checkpoint,
            finalized_checkpoint=finalized_checkpoint,
            highest_observed_checkpoint=highest_observed_checkpoint,
            watermark_value=watermark_value,
        )
        value = object.__new__(cls)
        object.__setattr__(value, "_exact_local_checkpoint_bytes", exact_inputs[0])
        object.__setattr__(value, "_exact_finalized_checkpoint_bytes", exact_inputs[1])
        object.__setattr__(value, "_exact_highest_observed_checkpoint_bytes", exact_inputs[2])
        object.__setattr__(value, "_exact_watermark_bytes", exact_inputs[3])
        object.__setattr__(value, "_relation", relation)
        object.__setattr__(value, "_blocker_code", blocker)
        object.__setattr__(value, "_local_database_revision", local_revision)
        object.__setattr__(value, "_highest_observed_database_revision", observed_revision)
        object.__setattr__(value, "_canonical_assessment_bytes", canonical)
        object.__setattr__(value, "_assessment_sha256", hashlib.sha256(canonical).digest())
        return value

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("release-currentness assessment cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("release-currentness assessment is immutable")

    def __delattr__(self, _name: str) -> NoReturn:
        raise TypeError("release-currentness assessment is immutable")

    def __bool__(self) -> NoReturn:
        raise TypeError("release-currentness assessment requires explicit disposition handling")

    def __copy__(self) -> NoReturn:
        raise TypeError("release-currentness assessment cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("release-currentness assessment cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("release-currentness assessment cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("release-currentness assessment cannot be serialized")

    def __getstate__(self) -> NoReturn:
        raise TypeError("release-currentness assessment cannot be serialized")

    @property
    def disposition(self) -> ReleaseCurrentnessDispositionV1:
        self._revalidated_assessment()
        return ReleaseCurrentnessDispositionV1.PAUSED

    @property
    def relation(self) -> ReleaseCurrentnessRelationV1:
        self._revalidated_assessment()
        return self._relation

    @property
    def blocker_code(self) -> str:
        self._revalidated_assessment()
        return self._blocker_code

    @property
    def local_database_revision(self) -> int:
        self._revalidated_assessment()
        return self._local_database_revision

    @property
    def highest_observed_database_revision(self) -> int:
        self._revalidated_assessment()
        return self._highest_observed_database_revision

    @property
    def canonical_assessment_bytes(self) -> bytes:
        self._revalidated_assessment()
        return self._canonical_assessment_bytes

    @property
    def assessment_sha256(self) -> bytes:
        self._revalidated_assessment()
        return self._assessment_sha256

    def _revalidated_assessment(self) -> None:
        try:
            local = _parse_checkpoint(self._exact_local_checkpoint_bytes, name="local")
            finalized = _parse_checkpoint(self._exact_finalized_checkpoint_bytes, name="finalized")
            observed = _parse_checkpoint(
                self._exact_highest_observed_checkpoint_bytes,
                name="highest_observed",
            )
            watermark_value = parse_exact_spot_v7_highest_observed_release_event_watermark_v1(
                self._exact_watermark_bytes
            )
            _validate_scope(local, finalized, observed, watermark_value)
            _validate_finalized_to_observed(finalized, observed)
            _validate_watermark_binding(watermark_value, finalized, observed)
            relation, blocker_code = _classify(local, finalized, observed)
            canonical = _canonical_assessment_bytes(
                exact_inputs=(
                    self._exact_local_checkpoint_bytes,
                    self._exact_finalized_checkpoint_bytes,
                    self._exact_highest_observed_checkpoint_bytes,
                    self._exact_watermark_bytes,
                ),
                relation=relation,
                blocker_code=blocker_code,
                local_checkpoint=local,
                finalized_checkpoint=finalized,
                highest_observed_checkpoint=observed,
                watermark_value=watermark_value,
            )
        except (TypeError, ValueError) as exc:
            raise ValueError("release-currentness assessment was mutated") from exc
        if (
            self._local_database_revision != local.database_revision
            or self._highest_observed_database_revision != observed.database_revision
            or self._relation is not relation
            or self._blocker_code != blocker_code
            or canonical != self._canonical_assessment_bytes
            or hashlib.sha256(canonical).digest() != self._assessment_sha256
        ):
            raise ValueError("release-currentness assessment was mutated")


def assess_exact_spot_v7_release_currentness_against_watermark_v1(
    *,
    exact_local_checkpoint_bytes: bytes,
    exact_finalized_checkpoint_bytes: bytes,
    exact_highest_observed_checkpoint_bytes: bytes,
    exact_watermark_bytes: bytes,
) -> _AuthorityNeutralReleaseCurrentnessAssessmentV1:
    """Classify exact bytes and always return an authority-neutral PAUSED result."""

    exact_inputs = _require_exact_input_bytes(
        exact_local_checkpoint_bytes=exact_local_checkpoint_bytes,
        exact_finalized_checkpoint_bytes=exact_finalized_checkpoint_bytes,
        exact_highest_observed_checkpoint_bytes=exact_highest_observed_checkpoint_bytes,
        exact_watermark_bytes=exact_watermark_bytes,
    )
    local = _parse_checkpoint(exact_inputs[0], name="local")
    finalized = _parse_checkpoint(exact_inputs[1], name="finalized")
    observed = _parse_checkpoint(exact_inputs[2], name="highest_observed")
    watermark_value = parse_exact_spot_v7_highest_observed_release_event_watermark_v1(
        exact_inputs[3]
    )
    _validate_scope(local, finalized, observed, watermark_value)
    _validate_finalized_to_observed(finalized, observed)
    _validate_watermark_binding(watermark_value, finalized, observed)
    relation, blocker_code = _classify(local, finalized, observed)
    return _AuthorityNeutralReleaseCurrentnessAssessmentV1._from_checked(
        exact_local_checkpoint_bytes=exact_inputs[0],
        exact_finalized_checkpoint_bytes=exact_inputs[1],
        exact_highest_observed_checkpoint_bytes=exact_inputs[2],
        exact_watermark_bytes=exact_inputs[3],
        relation=relation,
        blocker_code=blocker_code,
        local_database_revision=local.database_revision,
        highest_observed_database_revision=observed.database_revision,
        local_checkpoint=local,
        finalized_checkpoint=finalized,
        highest_observed_checkpoint=observed,
        watermark_value=watermark_value,
        seal=_RELEASE_CURRENTNESS_ASSESSMENT_SEAL_V1,
    )


def _validate_scope(
    local: checkpoint.SpotV7ReleaseStateCheckpointV1,
    finalized: checkpoint.SpotV7ReleaseStateCheckpointV1,
    observed: checkpoint.SpotV7ReleaseStateCheckpointV1,
    watermark_value: SpotV7HighestObservedReleaseEventWatermarkV1,
) -> None:
    values = (local, finalized, observed, watermark_value)
    for field in (
        "application_id",
        "chain_id",
        "domain_id",
        "release_profile",
        "store_identity_hash",
    ):
        expected = getattr(finalized, field)
        if any(getattr(value, field) != expected for value in values):
            raise _reject("SCOPE_MISMATCH", f"currentness inputs disagree on {field}")


def _validate_finalized_to_observed(
    finalized: checkpoint.SpotV7ReleaseStateCheckpointV1,
    observed: checkpoint.SpotV7ReleaseStateCheckpointV1,
) -> None:
    if observed.database_revision == finalized.database_revision:
        if observed.canonical_bytes != finalized.canonical_bytes:
            raise _reject(
                "FINALIZED_OBSERVED_CONFLICT",
                "equal revisions require the exact same finalized and observed checkpoint",
            )
        return
    if observed.database_revision != finalized.database_revision + 1:
        raise _reject(
            "OBSERVED_FINALIZED_DISTANCE_UNSUPPORTED",
            "V1 supports at most one highest-observed event after finality",
        )
    try:
        checkpoint.validate_spot_v7_release_state_checkpoint_successor_v1(finalized, observed)
    except checkpoint.SpotV7ReleaseStateCheckpointRejectV1 as exc:
        raise _reject(
            "OBSERVED_CHECKPOINT_NOT_SUCCESSOR",
            f"highest-observed checkpoint is not the exact finalized successor: {exc.code}",
        ) from exc


def _validate_watermark_binding(
    value: SpotV7HighestObservedReleaseEventWatermarkV1,
    finalized: checkpoint.SpotV7ReleaseStateCheckpointV1,
    observed: checkpoint.SpotV7ReleaseStateCheckpointV1,
) -> None:
    exact_fields: tuple[tuple[str, object, object], ...] = (
        (
            "latest_finalized_checkpoint_hash",
            value.latest_finalized_checkpoint_hash,
            finalized.release_checkpoint_hash,
        ),
        (
            "latest_finalized_database_revision",
            value.latest_finalized_database_revision,
            finalized.database_revision,
        ),
        (
            "highest_observed_checkpoint_hash",
            value.highest_observed_checkpoint_hash,
            observed.release_checkpoint_hash,
        ),
        (
            "highest_observed_database_revision",
            value.highest_observed_database_revision,
            observed.database_revision,
        ),
        (
            "highest_observed_release_state_root",
            value.highest_observed_release_state_root,
            observed.release_state_root,
        ),
        (
            "highest_observed_event_kind",
            value.highest_observed_event_kind,
            _checkpoint_event_kind(observed),
        ),
        (
            "highest_observed_select_input_id",
            value.highest_observed_select_input_id,
            observed.current_select_input_id,
        ),
        (
            "highest_observed_revocation_record_id",
            value.highest_observed_revocation_record_id,
            observed.current_revocation_record_id,
        ),
    )
    for field, actual, expected in exact_fields:
        if actual != expected:
            raise _reject(
                "WATERMARK_CHECKPOINT_BINDING_MISMATCH",
                f"watermark changes {field}",
            )


def _classify(
    local: checkpoint.SpotV7ReleaseStateCheckpointV1,
    finalized: checkpoint.SpotV7ReleaseStateCheckpointV1,
    observed: checkpoint.SpotV7ReleaseStateCheckpointV1,
) -> tuple[ReleaseCurrentnessRelationV1, str]:
    if local.database_revision < finalized.database_revision:
        return (
            ReleaseCurrentnessRelationV1.LOCAL_BEHIND_FINALIZED,
            "LOCAL_RELEASE_STATE_ROLLBACK_OR_INCOMPLETE",
        )
    if local.database_revision == finalized.database_revision:
        if local.canonical_bytes != finalized.canonical_bytes:
            return ReleaseCurrentnessRelationV1.LOCAL_FORK_AT_FINALIZED, "LOCAL_RELEASE_STATE_FORK"
        if observed.database_revision > finalized.database_revision:
            if observed.is_revoked:
                return (
                    ReleaseCurrentnessRelationV1.LOCAL_MATCHES_FINALIZED_BEHIND_PENDING_REVOCATION,
                    "PENDING_REVOCATION_WATERMARK_UNAUTHENTICATED",
                )
            return (
                ReleaseCurrentnessRelationV1.LOCAL_MATCHES_FINALIZED_BEHIND_PENDING_SELECTION,
                "PENDING_SELECTION_WATERMARK_UNAUTHENTICATED",
            )
    if local.database_revision > observed.database_revision:
        return (
            ReleaseCurrentnessRelationV1.LOCAL_AHEAD_OF_HIGHEST_OBSERVED,
            "HIGHEST_OBSERVED_WATERMARK_STALE",
        )
    if local.database_revision == observed.database_revision:
        if local.canonical_bytes != observed.canonical_bytes:
            return (
                ReleaseCurrentnessRelationV1.LOCAL_FORK_AT_HIGHEST_OBSERVED,
                "LOCAL_RELEASE_STATE_FORK",
            )
        if observed.is_genesis:
            return ReleaseCurrentnessRelationV1.LOCAL_MATCHES_GENESIS, "GENESIS_NOT_OPERATIONAL"
        if observed.is_revoked:
            return (
                ReleaseCurrentnessRelationV1.LOCAL_MATCHES_REVOKED_HIGHEST_OBSERVED,
                "REVOKED_RELEASE_WATERMARK_UNAUTHENTICATED",
            )
        if observed.database_revision > finalized.database_revision:
            return (
                ReleaseCurrentnessRelationV1.LOCAL_MATCHES_PENDING_SELECTION,
                "PENDING_SELECTION_WATERMARK_UNAUTHENTICATED",
            )
        return (
            ReleaseCurrentnessRelationV1.LOCAL_MATCHES_FINALIZED_SELECTION,
            "EXTERNAL_WATERMARK_AND_FINALITY_AUTHENTICATION_REQUIRED",
        )
    raise _reject("LOCAL_RELATION_UNREPRESENTABLE", "local checkpoint relation is unsupported")


def _canonical_assessment_bytes(
    *,
    exact_inputs: tuple[bytes, bytes, bytes, bytes],
    relation: ReleaseCurrentnessRelationV1,
    blocker_code: str,
    local_checkpoint: checkpoint.SpotV7ReleaseStateCheckpointV1,
    finalized_checkpoint: checkpoint.SpotV7ReleaseStateCheckpointV1,
    highest_observed_checkpoint: checkpoint.SpotV7ReleaseStateCheckpointV1,
    watermark_value: SpotV7HighestObservedReleaseEventWatermarkV1,
) -> bytes:
    body: dict[str, object] = {
        "blocker_code": blocker_code,
        "disposition": ReleaseCurrentnessDispositionV1.PAUSED.value,
        "external_backend_commitment": watermark_value.external_backend_commitment,
        "external_backend_id": watermark_value.external_backend_id,
        "external_finality_authenticated": False,
        "external_monotonicity_authenticated": False,
        "external_position": watermark_value.external_position,
        "finalized_checkpoint_hash": finalized_checkpoint.release_checkpoint_hash,
        "finalized_checkpoint_sha256": hashlib.sha256(exact_inputs[1]).hexdigest(),
        "finalized_database_revision": finalized_checkpoint.database_revision,
        "highest_observed_checkpoint_hash": (highest_observed_checkpoint.release_checkpoint_hash),
        "highest_observed_checkpoint_sha256": hashlib.sha256(exact_inputs[2]).hexdigest(),
        "highest_observed_database_revision": (highest_observed_checkpoint.database_revision),
        "highest_observed_event_kind": _checkpoint_event_kind(highest_observed_checkpoint).value,
        "highest_observed_release_state_root": (highest_observed_checkpoint.release_state_root),
        "local_checkpoint_hash": local_checkpoint.release_checkpoint_hash,
        "local_checkpoint_sha256": hashlib.sha256(exact_inputs[0]).hexdigest(),
        "local_database_revision": local_checkpoint.database_revision,
        "local_release_state_root": local_checkpoint.release_state_root,
        "production_authority": False,
        "relation": relation.value,
        "release_authority": False,
        "rollback_safe_currentness_established": False,
        "runtime_authority": False,
        "schema": AUTHORITY_NEUTRAL_RELEASE_CURRENTNESS_ASSESSMENT_SCHEMA_V1,
        "settlement_authority": False,
        "store_derived_checkpoint_provenance_verified": False,
        "watermark_hash": watermark_value.watermark_hash,
        "watermark_sha256": hashlib.sha256(exact_inputs[3]).hexdigest(),
    }
    document = dict(body)
    document["assessment_hash"] = hashlib.sha256(
        _ASSESSMENT_HASH_DOMAIN_V1 + encode_bytes(canonical_json_bytes(body))
    ).hexdigest()
    return canonical_json_bytes(document) + b"\n"


def _validate_watermark_shape(document: dict[str, object]) -> ObservedReleaseEventKindV1:
    position = _require_u64(document["external_position"], name="external_position")
    parent = _require_digest_allow_zero(
        document["external_parent_commitment"],
        name="external_parent_commitment",
    )
    if (position == 0) != (parent == ZERO_DIGEST_HEX_V1):
        raise _reject(
            "EXTERNAL_PARENT_POSITION_MISMATCH",
            "only external position zero may use the zero parent commitment",
        )
    finalized_revision = _require_u64(
        document["latest_finalized_database_revision"],
        name="latest_finalized_database_revision",
    )
    observed_revision = _require_u64(
        document["highest_observed_database_revision"],
        name="highest_observed_database_revision",
    )
    finalized_hash = _require_digest(
        document["latest_finalized_checkpoint_hash"],
        name="latest_finalized_checkpoint_hash",
    )
    observed_hash = _require_digest(
        document["highest_observed_checkpoint_hash"],
        name="highest_observed_checkpoint_hash",
    )
    if finalized_revision > observed_revision:
        raise _reject(
            "FINALIZED_AHEAD_OF_OBSERVED",
            "latest finalized revision cannot exceed highest observed revision",
        )
    if finalized_revision == observed_revision and finalized_hash != observed_hash:
        raise _reject(
            "FINALIZED_OBSERVED_CONFLICT",
            "equal finalized and observed revisions require one checkpoint hash",
        )
    event_kind = _parse_event_kind(document["highest_observed_event_kind"])
    select_id = _require_optional_digest(
        document["highest_observed_select_input_id"],
        name="highest_observed_select_input_id",
    )
    revocation_id = _require_optional_digest(
        document["highest_observed_revocation_record_id"],
        name="highest_observed_revocation_record_id",
    )
    if event_kind is ObservedReleaseEventKindV1.GENESIS:
        if observed_revision != 0 or select_id is not None or revocation_id is not None:
            raise _reject("GENESIS_EVENT_SHAPE", "genesis watermark event shape is invalid")
    elif event_kind is ObservedReleaseEventKindV1.SELECT:
        if observed_revision == 0 or select_id is None or revocation_id is not None:
            raise _reject("SELECT_EVENT_SHAPE", "SELECT watermark event shape is invalid")
    elif observed_revision == 0 or select_id is None or revocation_id is None:
        raise _reject("REVOKE_EVENT_SHAPE", "REVOKE watermark event shape is invalid")
    _require_token(document["application_id"], name="application_id")
    _require_token(document["chain_id"], name="chain_id")
    _require_token(document["domain_id"], name="domain_id")
    _require_token(document["release_profile"], name="release_profile")
    _require_token(document["external_backend_id"], name="external_backend_id")
    _require_digest(document["store_identity_hash"], name="store_identity_hash")
    _require_digest(
        document["external_backend_commitment"],
        name="external_backend_commitment",
    )
    _require_digest(
        document["highest_observed_release_state_root"],
        name="highest_observed_release_state_root",
    )
    return event_kind


def _decode_exact_watermark(raw: bytes) -> dict[str, object]:
    if type(raw) is not bytes:
        raise _reject("WATERMARK_TYPE", "highest-observed watermark must be exact bytes")
    if not raw or len(raw) > MAX_HIGHEST_OBSERVED_WATERMARK_BYTES_V1:
        raise _reject("WATERMARK_SIZE", "highest-observed watermark is empty or oversized")
    _require_bounded_json_depth(raw)
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as exc:
        raise _reject("ASCII_REQUIRED", "highest-observed watermark must be ASCII") from exc
    try:
        value = json.loads(
            text,
            object_pairs_hook=_reject_duplicate_keys,
            parse_float=_reject_float,
            parse_constant=_reject_nonfinite,
        )
    except SpotV7HighestObservedReleaseEventWatermarkRejectV1:
        raise
    except (json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise _reject("INVALID_JSON", "highest-observed watermark is invalid JSON") from exc
    if type(value) is not dict or frozenset(value) != _WATERMARK_FIELDS_V1:
        actual = frozenset(value) if type(value) is dict else frozenset()
        raise _reject(
            "FIELD_SET_MISMATCH",
            f"watermark missing={sorted(_WATERMARK_FIELDS_V1 - actual)} "
            f"extra={sorted(actual - _WATERMARK_FIELDS_V1)}",
        )
    if value["schema"] != HIGHEST_OBSERVED_RELEASE_EVENT_WATERMARK_SCHEMA_V1:
        raise _reject("SCHEMA_MISMATCH", "highest-observed watermark schema is unsupported")
    if canonical_json_bytes(value) + b"\n" != raw:
        raise _reject("NONCANONICAL_JSON", "highest-observed watermark is not canonical JSON")
    return value


def _parse_checkpoint(
    raw: bytes,
    *,
    name: str,
) -> checkpoint.SpotV7ReleaseStateCheckpointV1:
    if type(raw) is not bytes:
        raise _reject("CHECKPOINT_TYPE", f"{name} checkpoint must be exact bytes")
    try:
        return checkpoint.parse_exact_spot_v7_release_state_checkpoint_v1(raw)
    except checkpoint.SpotV7ReleaseStateCheckpointRejectV1 as exc:
        raise _reject(
            "CHECKPOINT_REJECTED",
            f"{name} checkpoint rejected: {exc.code}",
        ) from exc


def _require_exact_input_bytes(
    *,
    exact_local_checkpoint_bytes: bytes,
    exact_finalized_checkpoint_bytes: bytes,
    exact_highest_observed_checkpoint_bytes: bytes,
    exact_watermark_bytes: bytes,
) -> tuple[bytes, bytes, bytes, bytes]:
    values = (
        exact_local_checkpoint_bytes,
        exact_finalized_checkpoint_bytes,
        exact_highest_observed_checkpoint_bytes,
        exact_watermark_bytes,
    )
    if any(type(value) is not bytes for value in values):
        raise TypeError("release-currentness inputs must be exact bytes")
    return values


def _checkpoint_event_kind(
    value: checkpoint.SpotV7ReleaseStateCheckpointV1,
) -> ObservedReleaseEventKindV1:
    if value.is_genesis:
        return ObservedReleaseEventKindV1.GENESIS
    if value.is_revoked:
        return ObservedReleaseEventKindV1.REVOKE
    return ObservedReleaseEventKindV1.SELECT


def _watermark_hash(body: dict[str, object]) -> str:
    return hashlib.sha256(
        _WATERMARK_HASH_DOMAIN_V1 + encode_bytes(canonical_json_bytes(body))
    ).hexdigest()


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
            if depth > MAX_HIGHEST_OBSERVED_WATERMARK_DEPTH_V1:
                raise _reject("JSON_DEPTH", "highest-observed watermark is too deeply nested")
        elif byte in {0x5D, 0x7D}:
            depth -= 1
            if depth < 0:
                raise _reject("INVALID_JSON", "highest-observed watermark framing is invalid")
    if depth != 0 or in_string or escaped:
        raise _reject("INVALID_JSON", "highest-observed watermark framing is invalid")


def _require_u64(value: object, *, name: str) -> int:
    if type(value) is not int or not 0 <= value <= MAX_U64_V1:
        raise _reject("U64_REQUIRED", f"{name} must be a u64")
    return value


def _require_token(value: object, *, name: str) -> str:
    if type(value) is not str or _TOKEN_RE.fullmatch(value) is None:
        raise _reject("TOKEN_REQUIRED", f"{name} must be a bounded ASCII token")
    return value


def _require_digest(value: object, *, name: str) -> str:
    output = _require_digest_allow_zero(value, name=name)
    if output == ZERO_DIGEST_HEX_V1:
        raise _reject("NONZERO_DIGEST_REQUIRED", f"{name} must be nonzero")
    return output


def _require_digest_allow_zero(value: object, *, name: str) -> str:
    if type(value) is not str or _DIGEST_RE.fullmatch(value) is None:
        raise _reject("DIGEST_REQUIRED", f"{name} must be canonical lowercase hex")
    return value


def _require_optional_digest(value: object, *, name: str) -> str | None:
    if value is None:
        return None
    return _require_digest(value, name=name)


def _require_event_kind_input(value: object) -> ObservedReleaseEventKindV1:
    if type(value) is not ObservedReleaseEventKindV1:
        raise TypeError("highest_observed_event_kind must be the exact V1 enum")
    return value


def _parse_event_kind(value: object) -> ObservedReleaseEventKindV1:
    if type(value) is not str:
        raise _reject("EVENT_KIND_REQUIRED", "highest-observed event kind must be a string")
    try:
        return ObservedReleaseEventKindV1(value)
    except ValueError as exc:
        raise _reject("EVENT_KIND_REQUIRED", "highest-observed event kind is unsupported") from exc


def _reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    output: dict[str, object] = {}
    for key, value in pairs:
        if key in output:
            raise _reject("DUPLICATE_JSON_KEY", "watermark contains a duplicate JSON key")
        output[key] = value
    return output


def _reject_float(value: str) -> NoReturn:
    raise _reject("FLOAT_FORBIDDEN", value)


def _reject_nonfinite(value: str) -> NoReturn:
    raise _reject("NONFINITE_FORBIDDEN", value)


__all__ = [
    "AUTHORITY_NEUTRAL_RELEASE_CURRENTNESS_ASSESSMENT_SCHEMA_V1",
    "HIGHEST_OBSERVED_RELEASE_EVENT_WATERMARK_SCHEMA_V1",
    "MAX_HIGHEST_OBSERVED_WATERMARK_BYTES_V1",
    "ObservedReleaseEventKindV1",
    "ReleaseCurrentnessDispositionV1",
    "ReleaseCurrentnessRelationV1",
    "SpotV7HighestObservedReleaseEventWatermarkRejectV1",
    "SpotV7HighestObservedReleaseEventWatermarkV1",
    "assess_exact_spot_v7_release_currentness_against_watermark_v1",
    "build_spot_v7_highest_observed_release_event_watermark_v1",
    "parse_exact_spot_v7_highest_observed_release_event_watermark_v1",
]
