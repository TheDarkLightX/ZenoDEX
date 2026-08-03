"""Non-authoritative source observations and content-parity receipts for M6."""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from typing import Final, TypeAlias, cast, final
from weakref import WeakValueDictionary

from ..core.fcis_m6_global_state_projection_v1 import (
    M6_KNOWN_GLOBAL_PROJECTION_GAPS_V1,
    M6_PROJECTION_AUTHORITY_OBLIGATIONS_V1,
    M6GlobalProjectionGapV1,
    M6GlobalStateProjectionRejectCodeV1,
    M6GlobalStateProjectionRejectV1,
    M6ProjectionAuthorityObligationV1,
    M6ProjectionCoverageV1,
)
from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from .fcis_m6_projection_values_v1 import (
    M6_APPLICATION_COMPONENT_REGISTRY_ROOT_V1,
    M6ApplicationContentV1,
    _content_root_v1,
    _digest32,
    is_verified_application_content_v1,
)

M6_CONTENT_OBSERVATION_SCHEMA_V1: Final = "zenodex/fcis/m6/content-observation/v1"
M6_CONTENT_PARITY_SCHEMA_V1: Final = "zenodex/fcis/m6/content-parity/v1"

_OBSERVATION_TOKEN_V1 = object()
_PARITY_TOKEN_V1 = object()


class M6ProjectionSourceKindV1(str, Enum):
    TAU_CLAIMED_VIEW = "tau_claimed_view"
    ZENO_LEDGER_HEADER_STATE_COMMITMENT = "zeno_ledger_header_state_commitment"


@final
@dataclass(frozen=True, slots=True)
class M6ProjectionSourceDescriptorV1:
    """Claimed source coordinates retained without granting source authority."""

    source_kind: M6ProjectionSourceKindV1
    source_schema: str
    source_version: int
    source_state_root: str
    source_commitment_root: str
    source_chain_id: str | None
    claimed_source_position: int

    def __post_init__(self) -> None:
        if type(self.source_kind) is not M6ProjectionSourceKindV1:
            raise TypeError("source_kind must be exact")
        if type(self.source_schema) is not str or not self.source_schema:
            raise TypeError("source_schema must be an exact nonempty string")
        if type(self.source_version) is not int or self.source_version <= 0:
            raise TypeError("source_version must be an exact positive integer")
        _digest32(self.source_state_root, "source_state_root")
        _digest32(self.source_commitment_root, "source_commitment_root")
        if self.source_chain_id is not None and (
            type(self.source_chain_id) is not str or not self.source_chain_id
        ):
            raise TypeError("source_chain_id must be null or an exact nonempty string")
        if type(self.claimed_source_position) is not int or self.claimed_source_position < 0:
            raise TypeError("claimed_source_position must be an exact nonnegative integer")


def _observation_root_v1(
    source: M6ProjectionSourceDescriptorV1,
    content_root: str,
    obligations: tuple[M6ProjectionAuthorityObligationV1, ...],
) -> str:
    return sha256_hex(
        domain_sep_bytes("fcis_m6_content_observation", version=1)
        + canonical_json_bytes(
            {
                "schema": M6_CONTENT_OBSERVATION_SCHEMA_V1,
                "source_kind": source.source_kind.value,
                "source_schema": source.source_schema,
                "source_version": source.source_version,
                "source_state_root": source.source_state_root,
                "source_commitment_root": source.source_commitment_root,
                "source_chain_id": source.source_chain_id,
                "claimed_source_position": source.claimed_source_position,
                "content_root": content_root,
                "unmet_authority_obligations": [item.value for item in obligations],
            }
        )
    )


@final
@dataclass(frozen=True, slots=True, weakref_slot=True)
class M6ProjectionContentObservationV1:
    """Internally consistent content; it is not a current-source proof."""

    source: M6ProjectionSourceDescriptorV1
    content: M6ApplicationContentV1
    unmet_authority_obligations: tuple[M6ProjectionAuthorityObligationV1, ...]
    observation_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _OBSERVATION_TOKEN_V1:
            raise TypeError("content observation requires source admission")
        if type(self.source) is not M6ProjectionSourceDescriptorV1:
            raise TypeError("source descriptor must be exact")
        self.source.__post_init__()
        if not is_verified_application_content_v1(self.content):
            raise ValueError("observation content lacks decoding provenance")
        expected = tuple(
            item
            for item in M6_PROJECTION_AUTHORITY_OBLIGATIONS_V1
            if item in self.unmet_authority_obligations
        )
        if self.unmet_authority_obligations != expected:
            raise ValueError("unmet authority obligations must be unique and canonical")
        _digest32(self.observation_root, "observation_root")
        if self.observation_root != _observation_root_v1(
            self.source,
            self.content.content_root,
            self.unmet_authority_obligations,
        ):
            raise ValueError("observation_root does not rederive")

    @property
    def source_kind(self) -> M6ProjectionSourceKindV1:
        return self.source.source_kind

    @property
    def source_schema(self) -> str:
        return self.source.source_schema

    @property
    def source_version(self) -> int:
        return self.source.source_version

    @property
    def source_state_root(self) -> str:
        return self.source.source_state_root

    @property
    def source_commitment_root(self) -> str:
        return self.source.source_commitment_root

    @property
    def source_chain_id(self) -> str | None:
        return self.source.source_chain_id

    @property
    def claimed_source_position(self) -> int:
        return self.source.claimed_source_position


_OBSERVATIONS_V1: WeakValueDictionary[int, M6ProjectionContentObservationV1] = WeakValueDictionary()
_OBSERVATION_SNAPSHOTS_V1: dict[int, tuple[object, ...]] = {}


def _observation_snapshot_v1(value: M6ProjectionContentObservationV1) -> tuple[object, ...]:
    return (
        value.source,
        value.content.content_root,
        value.unmet_authority_obligations,
        value.observation_root,
    )


def _build_observation_v1(
    *,
    source: M6ProjectionSourceDescriptorV1,
    content: M6ApplicationContentV1,
    unmet_authority_obligations: tuple[M6ProjectionAuthorityObligationV1, ...],
) -> M6ProjectionContentObservationV1:
    value = M6ProjectionContentObservationV1(
        source=source,
        content=content,
        unmet_authority_obligations=unmet_authority_obligations,
        observation_root=_observation_root_v1(
            source,
            content.content_root,
            unmet_authority_obligations,
        ),
        _construction_token=_OBSERVATION_TOKEN_V1,
    )
    _OBSERVATIONS_V1[id(value)] = value
    _OBSERVATION_SNAPSHOTS_V1[id(value)] = _observation_snapshot_v1(value)
    return value


def is_verified_projection_content_observation_v1(value: object) -> bool:
    if type(value) is not M6ProjectionContentObservationV1:
        return False
    if _OBSERVATIONS_V1.get(id(value)) is not value:
        return False
    try:
        value.__post_init__(_OBSERVATION_TOKEN_V1)
        return _OBSERVATION_SNAPSHOTS_V1.get(id(value)) == _observation_snapshot_v1(value)
    except (TypeError, ValueError, ArithmeticError, OverflowError):
        return False


M6ContentObservationResultV1: TypeAlias = (
    M6ProjectionContentObservationV1 | M6GlobalStateProjectionRejectV1
)


def _parity_root_v1(tau_root: str, ledger_root: str, content_root: str) -> str:
    return sha256_hex(
        domain_sep_bytes("fcis_m6_content_parity", version=1)
        + canonical_json_bytes(
            {
                "schema": M6_CONTENT_PARITY_SCHEMA_V1,
                "component_registry_root": M6_APPLICATION_COMPONENT_REGISTRY_ROOT_V1,
                "tau_observation_root": tau_root,
                "zeno_ledger_observation_root": ledger_root,
                "content_root": content_root,
                "global_gaps": [gap.value for gap in M6_KNOWN_GLOBAL_PROJECTION_GAPS_V1],
                "unmet_authority_obligations": [
                    item.value for item in M6_PROJECTION_AUTHORITY_OBLIGATIONS_V1
                ],
            }
        )
    )


@final
@dataclass(frozen=True, slots=True, weakref_slot=True)
class M6ProjectionContentParityReceiptV1:
    """Same projected content under two structural commitment observations."""

    component_registry_root: str
    tau_observation_root: str
    zeno_ledger_observation_root: str
    content_root: str
    coverage: M6ProjectionCoverageV1
    global_gaps: tuple[M6GlobalProjectionGapV1, ...]
    unmet_authority_obligations: tuple[M6ProjectionAuthorityObligationV1, ...]
    parity_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _PARITY_TOKEN_V1:
            raise TypeError("content parity requires the parity verifier")
        for name in (
            "component_registry_root",
            "tau_observation_root",
            "zeno_ledger_observation_root",
            "content_root",
            "parity_root",
        ):
            _digest32(object.__getattribute__(self, name), name)
        if self.component_registry_root != M6_APPLICATION_COMPONENT_REGISTRY_ROOT_V1:
            raise ValueError("component registry root mismatch")
        if type(self.coverage) is not M6ProjectionCoverageV1:
            raise TypeError("coverage must be exact")
        self.coverage.__post_init__()
        if self.content_root != _content_root_v1(self.coverage):
            raise ValueError("content root does not bind coverage")
        if self.global_gaps != M6_KNOWN_GLOBAL_PROJECTION_GAPS_V1:
            raise ValueError("global gaps must equal the known-gap registry")
        if self.unmet_authority_obligations != M6_PROJECTION_AUTHORITY_OBLIGATIONS_V1:
            raise ValueError("parity must retain every unresolved authority obligation")
        if self.parity_root != _parity_root_v1(
            self.tau_observation_root,
            self.zeno_ledger_observation_root,
            self.content_root,
        ):
            raise ValueError("parity_root does not rederive")


_PARITIES_V1: WeakValueDictionary[int, M6ProjectionContentParityReceiptV1] = WeakValueDictionary()
_PARITY_SNAPSHOTS_V1: dict[int, tuple[object, ...]] = {}


def _parity_snapshot_v1(value: M6ProjectionContentParityReceiptV1) -> tuple[object, ...]:
    return (
        value.component_registry_root,
        value.tau_observation_root,
        value.zeno_ledger_observation_root,
        value.content_root,
        value.coverage.coverage_root,
        value.global_gaps,
        value.unmet_authority_obligations,
        value.parity_root,
    )


def is_verified_projection_content_parity_v1(value: object) -> bool:
    if type(value) is not M6ProjectionContentParityReceiptV1:
        return False
    if _PARITIES_V1.get(id(value)) is not value:
        return False
    try:
        value.__post_init__(_PARITY_TOKEN_V1)
        return _PARITY_SNAPSHOTS_V1.get(id(value)) == _parity_snapshot_v1(value)
    except (TypeError, ValueError, ArithmeticError, OverflowError):
        return False


M6ContentParityResultV1: TypeAlias = (
    M6ProjectionContentParityReceiptV1 | M6GlobalStateProjectionRejectV1
)


def _reject(
    code: M6GlobalStateProjectionRejectCodeV1,
    *path: str,
) -> M6GlobalStateProjectionRejectV1:
    return M6GlobalStateProjectionRejectV1(code, tuple(path))


def verify_tau_zeno_ledger_content_parity_v1(
    first: object,
    second: object,
) -> M6ContentParityResultV1:
    """Compare content only; positions and source authority remain unresolved."""

    if not is_verified_projection_content_observation_v1(first) or not (
        is_verified_projection_content_observation_v1(second)
    ):
        return _reject(M6GlobalStateProjectionRejectCodeV1.INVALID_SOURCE, "parity")
    observations = cast(
        tuple[M6ProjectionContentObservationV1, M6ProjectionContentObservationV1],
        (first, second),
    )
    by_kind = {observation.source_kind: observation for observation in observations}
    if set(by_kind) != {
        M6ProjectionSourceKindV1.TAU_CLAIMED_VIEW,
        M6ProjectionSourceKindV1.ZENO_LEDGER_HEADER_STATE_COMMITMENT,
    }:
        return _reject(
            M6GlobalStateProjectionRejectCodeV1.SOURCE_LINEAGE_MISMATCH,
            "parity",
            "source_kind",
        )
    tau = by_kind[M6ProjectionSourceKindV1.TAU_CLAIMED_VIEW]
    ledger = by_kind[M6ProjectionSourceKindV1.ZENO_LEDGER_HEADER_STATE_COMMITMENT]
    if tau.content.content_root != ledger.content.content_root:
        return _reject(
            M6GlobalStateProjectionRejectCodeV1.PROJECTION_MISMATCH,
            "parity",
            "content_root",
        )
    value = M6ProjectionContentParityReceiptV1(
        component_registry_root=M6_APPLICATION_COMPONENT_REGISTRY_ROOT_V1,
        tau_observation_root=tau.observation_root,
        zeno_ledger_observation_root=ledger.observation_root,
        content_root=tau.content.content_root,
        coverage=tau.content.coverage,
        global_gaps=M6_KNOWN_GLOBAL_PROJECTION_GAPS_V1,
        unmet_authority_obligations=M6_PROJECTION_AUTHORITY_OBLIGATIONS_V1,
        parity_root=_parity_root_v1(
            tau.observation_root,
            ledger.observation_root,
            tau.content.content_root,
        ),
        _construction_token=_PARITY_TOKEN_V1,
    )
    _PARITIES_V1[id(value)] = value
    _PARITY_SNAPSHOTS_V1[id(value)] = _parity_snapshot_v1(value)
    return value


__all__ = (
    "M6_CONTENT_OBSERVATION_SCHEMA_V1",
    "M6_CONTENT_PARITY_SCHEMA_V1",
    "M6ContentObservationResultV1",
    "M6ContentParityResultV1",
    "M6ProjectionContentObservationV1",
    "M6ProjectionContentParityReceiptV1",
    "M6ProjectionSourceDescriptorV1",
    "M6ProjectionSourceKindV1",
    "is_verified_projection_content_observation_v1",
    "is_verified_projection_content_parity_v1",
    "verify_tau_zeno_ledger_content_parity_v1",
)
