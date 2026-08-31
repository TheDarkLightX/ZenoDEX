"""Immutable reference types for GlobalSettlementABI V1.

This module is a deterministic Python projection of the modular whole-economy
contract.  It defines canonical values and structural invariants only.  It is
research evidence and grants no publication authority, proof validity, or M6
release status.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from enum import Enum
from typing import Final, Mapping, Protocol, runtime_checkable

from ..state.canonical import canonical_json_bytes, domain_sep_bytes

GLOBAL_SETTLEMENT_ABI_V1: Final = "zenodex/global-settlement-abi/v1"
FEE_RESIDUE_PRINCIPAL_V1: Final = "protocol:fee-unallocated-reserve"
FEE_RESIDUE_CONTROL_DOMAIN_V1: Final = "zenoledger:protocol-fee-residue"
MAX_TOKEN_BYTES_V1: Final = 160
MAX_ROUTE_MODULES_V1: Final = 8
MAX_EPOCH_COMMANDS_V1: Final = 64
MAX_EPOCH_LEAF_OCCURRENCES_V1: Final = 64
MAX_POLICY_BINDINGS_V1: Final = 256
MAX_JOURNAL_BYTES_V1: Final = 1_048_576
MAX_CYCLE_BUDGET_V1: Final = 1 << 40
MAX_U64_V1: Final = (1 << 64) - 1
MAX_ATOMS_V1: Final = (1 << 128) - 1
MIN_DELTA_ATOMS_V1: Final = -(1 << 127)
MAX_DELTA_ATOMS_V1: Final = (1 << 127) - 1
ZERO_ROOT_V1: Final = "0x" + "00" * 32


@runtime_checkable
class _Canonicalizable(Protocol):
    def to_canonical(self) -> object: ...


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if type(value) is not int or value < 0:
        raise ValueError(f"{name} must be a non-negative integer")
    if value > MAX_U64_V1:
        raise ValueError(f"{name} must fit an unsigned 64-bit integer")
    return value


def _require_positive_int(value: object, *, name: str) -> int:
    result = _require_nonnegative_int(value, name=name)
    if result == 0:
        raise ValueError(f"{name} must be positive")
    return result


def _require_atoms_u128(value: object, *, name: str) -> int:
    if type(value) is not int or value < 0:
        raise ValueError(f"{name} must be a non-negative integer")
    if value > MAX_ATOMS_V1:
        raise ValueError(f"{name} must fit an unsigned 128-bit integer")
    return value


def _require_delta_atoms_i128(value: object, *, name: str) -> int:
    if type(value) is not int:
        raise ValueError(f"{name} must be an integer")
    if not MIN_DELTA_ATOMS_V1 <= value <= MAX_DELTA_ATOMS_V1:
        raise ValueError(f"{name} must fit a signed 128-bit integer")
    return value


def _require_bool(value: object, *, name: str) -> bool:
    if type(value) is not bool:
        raise TypeError(f"{name} must be bool")
    return value


def _require_token(value: object, *, name: str) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be a string")
    if not value:
        raise ValueError(f"{name} must not be empty")
    if len(value.encode("utf-8")) > MAX_TOKEN_BYTES_V1:
        raise ValueError(f"{name} exceeds {MAX_TOKEN_BYTES_V1} UTF-8 bytes")
    if any(ord(char) < 0x21 or ord(char) > 0x7E for char in value):
        raise ValueError(f"{name} must use printable ASCII")
    return value


def _require_root(value: object, *, name: str, allow_zero: bool = False) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be a string")
    if len(value) != 66 or not value.startswith("0x") or value != value.lower():
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed 32-byte hex")
    try:
        bytes.fromhex(value[2:])
    except ValueError as exc:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed 32-byte hex") from exc
    if not allow_zero and value == ZERO_ROOT_V1:
        raise ValueError(f"{name} must be nonzero")
    return value


def _canonical_value(value: object) -> object:
    if value is None or type(value) in {bool, int, str}:
        return value
    if isinstance(value, Enum):
        return _canonical_value(value.value)
    if isinstance(value, bool | int | str):
        raise TypeError("canonical scalar subclasses are unsupported")
    if type(value) is tuple or type(value) is list:
        return [_canonical_value(item) for item in value]
    if isinstance(value, tuple | list):
        raise TypeError("canonical sequence subclasses are unsupported")
    if type(value) is dict:
        if any(type(key) is not str for key in value):
            raise TypeError("canonical mapping keys must be strings")
        return {
            key: _canonical_value(item)
            for key, item in sorted(value.items(), key=lambda pair: pair[0])
        }
    if isinstance(value, Mapping):
        raise TypeError("canonical mapping subclasses are unsupported")
    if isinstance(value, _Canonicalizable):
        return _canonical_value(value.to_canonical())
    raise TypeError("unsupported canonical value type")


def canonical_global_bytes_v1(value: object) -> bytes:
    """Encode a typed ABI value as deterministic canonical JSON."""

    encoded: object = canonical_json_bytes(_canonical_value(value))
    if type(encoded) is not bytes:
        raise TypeError("canonical encoder returned an invalid value")
    return encoded


def hash_global_v1(domain: str, value: object) -> str:
    """Hash a canonical value under a versioned ASCII domain."""

    _require_token(domain, name="hash domain")
    digest = hashlib.sha256()
    digest.update(domain_sep_bytes(domain, version=1))
    digest.update(canonical_global_bytes_v1(value))
    return "0x" + digest.hexdigest()


def canonical_economic_command_body_bytes_v1(
    command_kind: str,
    command: object,
) -> bytes:
    """Encode the exact typed command body signed and retained by ingress."""

    _require_token(command_kind, name="economic command body kind")
    return canonical_global_bytes_v1(
        {
            "command_kind": command_kind,
            "command": command,
        }
    )


def hash_economic_command_body_bytes_v1(command_body_bytes: bytes) -> str:
    """Hash exact canonical command bytes under the authenticated-body domain."""

    if type(command_body_bytes) is not bytes:
        raise TypeError("economic command body bytes must be exact bytes")
    if not command_body_bytes:
        raise ValueError("economic command body bytes must not be empty")
    digest = hashlib.sha256()
    digest.update(domain_sep_bytes("authenticated-economic-command-body-v1", version=1))
    digest.update(command_body_bytes)
    return "0x" + digest.hexdigest()


def hash_economic_command_body_v1(command_kind: str, command: object) -> str:
    """Commit one exact canonical typed command payload under the ABI domain."""

    return hash_economic_command_body_bytes_v1(
        canonical_economic_command_body_bytes_v1(command_kind, command)
    )


def _require_tuple(value: object, *, name: str) -> tuple[object, ...]:
    if type(value) is not tuple:
        raise TypeError(f"{name} must be a tuple")
    return value


def _require_sorted_unique_tokens(
    values: object,
    *,
    name: str,
    allow_empty: bool = True,
) -> tuple[str, ...]:
    items = _require_tuple(values, name=name)
    normalized = tuple(_require_token(item, name=f"{name}[{index}]") for index, item in enumerate(items))
    if not allow_empty and not normalized:
        raise ValueError(f"{name} must not be empty")
    if normalized != tuple(sorted(set(normalized))):
        raise ValueError(f"{name} must be sorted and unique")
    return normalized


def _require_semantic_order_unique(values: object, *, name: str) -> tuple[str, ...]:
    items = _require_tuple(values, name=name)
    normalized = tuple(_require_token(item, name=f"{name}[{index}]") for index, item in enumerate(items))
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{name} must be unique")
    return normalized


class LaneIdV1(str, Enum):
    ASSET_TRANSFER = "ASSET_TRANSFER"
    SPOT_LIQUIDITY = "SPOT_LIQUIDITY"
    FARM_INCENTIVES = "FARM_INCENTIVES"
    ZDEX_TOKENOMICS = "ZDEX_TOKENOMICS"
    ZUSD_MONETARY = "ZUSD_MONETARY"
    PERPS_MARKET = "PERPS_MARKET"
    ORACLE_MARKET = "ORACLE_MARKET"
    SEALED_AUCTION = "SEALED_AUCTION"
    STRATEGY_ESCROW = "STRATEGY_ESCROW"
    PROOF_REWARDS = "PROOF_REWARDS"
    EXTERNAL_CUSTODY = "EXTERNAL_CUSTODY"
    GOVERNANCE_MIGRATION = "GOVERNANCE_MIGRATION"


ALL_LANE_IDS_V1: Final = tuple(LaneIdV1)


class ReleaseStatusV1(str, Enum):
    CANDIDATE = "CANDIDATE"
    SHADOW = "SHADOW"
    ACTIVE_NEW = "ACTIVE_NEW"
    DRAIN_ONLY = "DRAIN_ONLY"
    VERIFY_ONLY = "VERIFY_ONLY"
    RETIRED = "RETIRED"
    REVOKED = "REVOKED"


class EvidenceStatusV1(str, Enum):
    SPECIFIED = "SPECIFIED"
    IMPLEMENTED = "IMPLEMENTED"
    PROVED = "PROVED"
    MOUNTED = "MOUNTED"
    TESTED = "TESTED"
    TERMINAL_COMPLETE = "TERMINAL_COMPLETE"
    MIGRATABLE = "MIGRATABLE"
    NO_BYPASS = "NO_BYPASS"
    RELEASE_BACKED = "RELEASE_BACKED"
    DISABLED_PROVED_NO_WRITER = "DISABLED_PROVED_NO_WRITER"


REQUIRED_ACTIVE_EVIDENCE_V1: Final = frozenset(
    {
        EvidenceStatusV1.SPECIFIED,
        EvidenceStatusV1.IMPLEMENTED,
        EvidenceStatusV1.PROVED,
        EvidenceStatusV1.MOUNTED,
        EvidenceStatusV1.TESTED,
        EvidenceStatusV1.TERMINAL_COMPLETE,
        EvidenceStatusV1.MIGRATABLE,
        EvidenceStatusV1.NO_BYPASS,
        EvidenceStatusV1.RELEASE_BACKED,
    }
)


class ProfileStatusV1(str, Enum):
    CANDIDATE = "CANDIDATE"
    SHADOW = "SHADOW"
    ACTIVE = "ACTIVE"
    RETIRED = "RETIRED"
    REVOKED = "REVOKED"


def _evidence_tuple(values: object, *, name: str) -> tuple[EvidenceStatusV1, ...]:
    items = _require_tuple(values, name=name)
    if any(type(item) is not EvidenceStatusV1 for item in items):
        raise TypeError(f"{name} contains an unknown status")
    statuses = tuple(item for item in items if type(item) is EvidenceStatusV1)
    expected = tuple(sorted(set(statuses), key=lambda item: item.value))
    if statuses != expected:
        raise ValueError(f"{name} must be sorted and unique")
    return statuses


@dataclass(frozen=True, slots=True)
class LaneModuleReleaseV1:
    lane_id: LaneIdV1
    release_id: str
    semantic_version: str
    state_schema_root: str
    command_variants: tuple[str, ...]
    terminal_command_variants: tuple[str, ...]
    guest_image_id: str
    specification_root: str
    source_root: str
    toolchain_root: str
    terminal_coverage_root: str
    migration_compatibility_root: str
    max_cycles: int
    max_journal_bytes: int
    status: ReleaseStatusV1
    accepts_new_objects: bool
    evidence_statuses: tuple[EvidenceStatusV1, ...] = ()

    def __post_init__(self) -> None:
        if type(self.lane_id) is not LaneIdV1:
            raise TypeError("lane release lane_id is not closed")
        _require_root(self.release_id, name="lane release id")
        _require_token(self.semantic_version, name="lane semantic version")
        _require_sorted_unique_tokens(self.command_variants, name="lane command variants")
        terminals = _require_sorted_unique_tokens(
            self.terminal_command_variants,
            name="lane terminal command variants",
        )
        if not set(terminals).issubset(self.command_variants):
            raise ValueError("lane terminal commands must be declared command variants")
        for field_name in (
            "state_schema_root",
            "guest_image_id",
            "specification_root",
            "source_root",
            "toolchain_root",
            "terminal_coverage_root",
            "migration_compatibility_root",
        ):
            _require_root(getattr(self, field_name), name=f"lane {field_name}")
        _require_positive_int(self.max_cycles, name="lane max_cycles")
        _require_positive_int(self.max_journal_bytes, name="lane max_journal_bytes")
        if self.max_cycles > MAX_CYCLE_BUDGET_V1:
            raise ValueError("lane max_cycles exceeds ABI V1 ceiling")
        if self.max_journal_bytes > MAX_JOURNAL_BYTES_V1:
            raise ValueError("lane max_journal_bytes exceeds ABI V1 ceiling")
        if type(self.status) is not ReleaseStatusV1:
            raise TypeError("lane release status is not closed")
        _require_bool(self.accepts_new_objects, name="lane accepts_new_objects")
        evidence = _evidence_tuple(self.evidence_statuses, name="lane evidence statuses")
        if EvidenceStatusV1.DISABLED_PROVED_NO_WRITER in evidence:
            if evidence != (EvidenceStatusV1.DISABLED_PROVED_NO_WRITER,):
                raise ValueError("proved-disabled lane evidence must be the only evidence status")
            if self.accepts_new_objects or self.status is ReleaseStatusV1.ACTIVE_NEW:
                raise ValueError("proved-disabled lane release cannot accept new objects")
        if self.accepts_new_objects and self.status is not ReleaseStatusV1.ACTIVE_NEW:
            raise ValueError("only ACTIVE_NEW lane releases may accept new objects")
        if self.status is ReleaseStatusV1.ACTIVE_NEW and not self.accepts_new_objects:
            raise ValueError("ACTIVE_NEW lane releases must accept new objects")
        if self.status in {ReleaseStatusV1.RETIRED, ReleaseStatusV1.REVOKED} and self.accepts_new_objects:
            raise ValueError("retired or revoked lane releases cannot accept new objects")
        if self.status is ReleaseStatusV1.ACTIVE_NEW and set(evidence) != REQUIRED_ACTIVE_EVIDENCE_V1:
            raise ValueError("ACTIVE_NEW lane release lacks the complete release evidence set")
        if self.release_id != self.derived_release_id:
            raise ValueError("lane release_id is not the exact content-derived id")

    @classmethod
    def build(
        cls,
        *,
        lane_id: LaneIdV1,
        semantic_version: str,
        state_schema_root: str,
        command_variants: tuple[str, ...],
        terminal_command_variants: tuple[str, ...],
        guest_image_id: str,
        specification_root: str,
        source_root: str,
        toolchain_root: str,
        terminal_coverage_root: str,
        migration_compatibility_root: str,
        max_cycles: int,
        max_journal_bytes: int,
        status: ReleaseStatusV1,
        accepts_new_objects: bool,
        evidence_statuses: tuple[EvidenceStatusV1, ...] = (),
    ) -> LaneModuleReleaseV1:
        if cls is not LaneModuleReleaseV1:
            raise TypeError("lane release factory requires the exact declared type")
        body = LaneModuleReleaseV1._content_body(
            lane_id=lane_id,
            state_schema_root=state_schema_root,
            command_variants=command_variants,
            terminal_command_variants=terminal_command_variants,
            guest_image_id=guest_image_id,
            specification_root=specification_root,
            source_root=source_root,
            toolchain_root=toolchain_root,
            terminal_coverage_root=terminal_coverage_root,
            migration_compatibility_root=migration_compatibility_root,
            max_cycles=max_cycles,
            max_journal_bytes=max_journal_bytes,
        )
        return LaneModuleReleaseV1(
            lane_id=lane_id,
            release_id=hash_global_v1("global-lane-module-release-content-v1", body),
            semantic_version=semantic_version,
            state_schema_root=state_schema_root,
            command_variants=command_variants,
            terminal_command_variants=terminal_command_variants,
            guest_image_id=guest_image_id,
            specification_root=specification_root,
            source_root=source_root,
            toolchain_root=toolchain_root,
            terminal_coverage_root=terminal_coverage_root,
            migration_compatibility_root=migration_compatibility_root,
            max_cycles=max_cycles,
            max_journal_bytes=max_journal_bytes,
            status=status,
            accepts_new_objects=accepts_new_objects,
            evidence_statuses=evidence_statuses,
        )

    @staticmethod
    def _content_body(**values: object) -> dict[str, object]:
        return {"schema": GLOBAL_SETTLEMENT_ABI_V1, **values}

    @property
    def derived_release_id(self) -> str:
        return hash_global_v1(
            "global-lane-module-release-content-v1",
            self._content_body(
                lane_id=self.lane_id,
                state_schema_root=self.state_schema_root,
                command_variants=self.command_variants,
                terminal_command_variants=self.terminal_command_variants,
                guest_image_id=self.guest_image_id,
                specification_root=self.specification_root,
                source_root=self.source_root,
                toolchain_root=self.toolchain_root,
                terminal_coverage_root=self.terminal_coverage_root,
                migration_compatibility_root=self.migration_compatibility_root,
                max_cycles=self.max_cycles,
                max_journal_bytes=self.max_journal_bytes,
            ),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            **self._content_body(
                lane_id=self.lane_id,
                state_schema_root=self.state_schema_root,
                command_variants=self.command_variants,
                terminal_command_variants=self.terminal_command_variants,
                guest_image_id=self.guest_image_id,
                specification_root=self.specification_root,
                source_root=self.source_root,
                toolchain_root=self.toolchain_root,
                terminal_coverage_root=self.terminal_coverage_root,
                migration_compatibility_root=self.migration_compatibility_root,
                max_cycles=self.max_cycles,
                max_journal_bytes=self.max_journal_bytes,
            ),
            "release_id": self.release_id,
            "semantic_version": self.semantic_version,
            "status": self.status,
            "accepts_new_objects": self.accepts_new_objects,
            "evidence_statuses": self.evidence_statuses,
        }


@dataclass(frozen=True, slots=True)
class LaneRegistryV1:
    releases: tuple[LaneModuleReleaseV1, ...]

    def __post_init__(self) -> None:
        _require_tuple(self.releases, name="lane registry releases")
        if any(type(item) is not LaneModuleReleaseV1 for item in self.releases):
            raise TypeError("lane registry contains an invalid release")
        actual = tuple(item.lane_id for item in self.releases)
        if actual != ALL_LANE_IDS_V1:
            raise ValueError("lane registry must contain every ABI V1 lane in canonical order")

    @property
    def registry_root(self) -> str:
        return hash_global_v1("global-lane-registry-v1", self.to_canonical())

    def release_for(self, lane_id: LaneIdV1) -> LaneModuleReleaseV1:
        if type(lane_id) is not LaneIdV1:
            raise ValueError("unknown lane id")
        return self.releases[ALL_LANE_IDS_V1.index(lane_id)]

    def to_canonical(self) -> dict[str, object]:
        return {"schema": GLOBAL_SETTLEMENT_ABI_V1, "releases": self.releases}


@dataclass(frozen=True, slots=True)
class LaneCoordinatorReleaseV1:
    lane_id: LaneIdV1
    coordinator_release_id: str
    semantic_version: str
    coordinator_schema_root: str
    guest_image_id: str
    specification_root: str
    source_root: str
    toolchain_root: str
    max_cycles: int
    max_journal_bytes: int
    status: ReleaseStatusV1
    accepts_new_objects: bool
    evidence_statuses: tuple[EvidenceStatusV1, ...] = ()

    def __post_init__(self) -> None:
        if type(self.lane_id) is not LaneIdV1:
            raise TypeError("lane coordinator lane_id is not closed")
        _require_root(self.coordinator_release_id, name="lane coordinator release id")
        _require_token(self.semantic_version, name="lane coordinator semantic version")
        for field_name in (
            "coordinator_schema_root",
            "guest_image_id",
            "specification_root",
            "source_root",
            "toolchain_root",
        ):
            _require_root(getattr(self, field_name), name=f"lane coordinator {field_name}")
        _require_positive_int(self.max_cycles, name="lane coordinator max_cycles")
        _require_positive_int(self.max_journal_bytes, name="lane coordinator max_journal_bytes")
        if self.max_cycles > MAX_CYCLE_BUDGET_V1:
            raise ValueError("lane coordinator max_cycles exceeds ABI V1 ceiling")
        if self.max_journal_bytes > MAX_JOURNAL_BYTES_V1:
            raise ValueError("lane coordinator max_journal_bytes exceeds ABI V1 ceiling")
        if type(self.status) is not ReleaseStatusV1:
            raise TypeError("lane coordinator release status is not closed")
        _require_bool(self.accepts_new_objects, name="lane coordinator accepts_new_objects")
        evidence = _evidence_tuple(
            self.evidence_statuses,
            name="lane coordinator evidence statuses",
        )
        if EvidenceStatusV1.DISABLED_PROVED_NO_WRITER in evidence:
            if evidence != (EvidenceStatusV1.DISABLED_PROVED_NO_WRITER,):
                raise ValueError("proved-disabled lane coordinator evidence must be the only status")
            if self.accepts_new_objects or self.status is ReleaseStatusV1.ACTIVE_NEW:
                raise ValueError("proved-disabled lane coordinator cannot accept new objects")
        if self.accepts_new_objects and self.status is not ReleaseStatusV1.ACTIVE_NEW:
            raise ValueError("only ACTIVE_NEW lane coordinators may accept new objects")
        if self.status is ReleaseStatusV1.ACTIVE_NEW and not self.accepts_new_objects:
            raise ValueError("ACTIVE_NEW lane coordinators must accept new objects")
        if self.status in {ReleaseStatusV1.RETIRED, ReleaseStatusV1.REVOKED} and self.accepts_new_objects:
            raise ValueError("retired or revoked lane coordinators cannot accept new objects")
        if self.status is ReleaseStatusV1.ACTIVE_NEW and set(evidence) != REQUIRED_ACTIVE_EVIDENCE_V1:
            raise ValueError("ACTIVE_NEW lane coordinator lacks the complete release evidence set")
        if self.coordinator_release_id != self.derived_coordinator_release_id:
            raise ValueError("coordinator_release_id is not the exact content-derived id")

    @classmethod
    def build(
        cls,
        *,
        lane_id: LaneIdV1,
        semantic_version: str,
        coordinator_schema_root: str,
        guest_image_id: str,
        specification_root: str,
        source_root: str,
        toolchain_root: str,
        max_cycles: int,
        max_journal_bytes: int,
        status: ReleaseStatusV1,
        accepts_new_objects: bool,
        evidence_statuses: tuple[EvidenceStatusV1, ...] = (),
    ) -> LaneCoordinatorReleaseV1:
        if cls is not LaneCoordinatorReleaseV1:
            raise TypeError("lane coordinator factory requires the exact declared type")
        body = LaneCoordinatorReleaseV1._content_body(
            lane_id=lane_id,
            coordinator_schema_root=coordinator_schema_root,
            guest_image_id=guest_image_id,
            specification_root=specification_root,
            source_root=source_root,
            toolchain_root=toolchain_root,
            max_cycles=max_cycles,
            max_journal_bytes=max_journal_bytes,
        )
        return LaneCoordinatorReleaseV1(
            lane_id=lane_id,
            coordinator_release_id=hash_global_v1(
                "global-lane-coordinator-release-content-v1",
                body,
            ),
            semantic_version=semantic_version,
            coordinator_schema_root=coordinator_schema_root,
            guest_image_id=guest_image_id,
            specification_root=specification_root,
            source_root=source_root,
            toolchain_root=toolchain_root,
            max_cycles=max_cycles,
            max_journal_bytes=max_journal_bytes,
            status=status,
            accepts_new_objects=accepts_new_objects,
            evidence_statuses=evidence_statuses,
        )

    @staticmethod
    def _content_body(**values: object) -> dict[str, object]:
        return {"schema": GLOBAL_SETTLEMENT_ABI_V1, **values}

    @property
    def derived_coordinator_release_id(self) -> str:
        return hash_global_v1(
            "global-lane-coordinator-release-content-v1",
            self._content_body(
                lane_id=self.lane_id,
                coordinator_schema_root=self.coordinator_schema_root,
                guest_image_id=self.guest_image_id,
                specification_root=self.specification_root,
                source_root=self.source_root,
                toolchain_root=self.toolchain_root,
                max_cycles=self.max_cycles,
                max_journal_bytes=self.max_journal_bytes,
            ),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            **self._content_body(
                lane_id=self.lane_id,
                coordinator_schema_root=self.coordinator_schema_root,
                guest_image_id=self.guest_image_id,
                specification_root=self.specification_root,
                source_root=self.source_root,
                toolchain_root=self.toolchain_root,
                max_cycles=self.max_cycles,
                max_journal_bytes=self.max_journal_bytes,
            ),
            "coordinator_release_id": self.coordinator_release_id,
            "semantic_version": self.semantic_version,
            "status": self.status,
            "accepts_new_objects": self.accepts_new_objects,
            "evidence_statuses": self.evidence_statuses,
        }


@dataclass(frozen=True, slots=True)
class LaneCoordinatorRegistryV1:
    releases: tuple[LaneCoordinatorReleaseV1, ...]

    def __post_init__(self) -> None:
        _require_tuple(self.releases, name="lane coordinator registry releases")
        if any(type(item) is not LaneCoordinatorReleaseV1 for item in self.releases):
            raise TypeError("lane coordinator registry contains an invalid release")
        actual = tuple(item.lane_id for item in self.releases)
        if actual != ALL_LANE_IDS_V1:
            raise ValueError(
                "lane coordinator registry must contain every ABI V1 lane in canonical order"
            )

    @property
    def registry_root(self) -> str:
        return hash_global_v1("global-lane-coordinator-registry-v1", self.to_canonical())

    def release_for(self, lane_id: LaneIdV1) -> LaneCoordinatorReleaseV1:
        if type(lane_id) is not LaneIdV1:
            raise ValueError("unknown lane id")
        return self.releases[ALL_LANE_IDS_V1.index(lane_id)]

    def to_canonical(self) -> dict[str, object]:
        return {"schema": GLOBAL_SETTLEMENT_ABI_V1, "releases": self.releases}


@dataclass(frozen=True, slots=True)
class RouteReleaseV1:
    route_release_id: str
    semantic_version: str
    command_kind: str
    ordered_lanes: tuple[LaneIdV1, ...]
    module_release_ids: tuple[str, ...]
    dependency_roles: tuple[str, ...]
    port_schema_roots: tuple[str, ...]
    guest_image_id: str
    specification_root: str
    source_root: str
    toolchain_root: str
    oracle_policy_root: str
    issue_burn_policy_root: str
    max_cycles: int
    max_journal_bytes: int
    status: ReleaseStatusV1
    accepts_new_objects: bool
    evidence_statuses: tuple[EvidenceStatusV1, ...] = ()

    def __post_init__(self) -> None:
        _require_root(self.route_release_id, name="route release id")
        _require_token(self.semantic_version, name="route semantic version")
        _require_token(self.command_kind, name="route command kind")
        _require_tuple(self.ordered_lanes, name="route ordered lanes")
        if not 1 <= len(self.ordered_lanes) <= MAX_ROUTE_MODULES_V1:
            raise ValueError("route must consume between one and eight module receipts")
        if any(type(item) is not LaneIdV1 for item in self.ordered_lanes):
            raise TypeError("route contains an unknown lane")
        if len(set(self.ordered_lanes)) != len(self.ordered_lanes):
            raise ValueError("route lanes must be unique")
        release_ids = _require_semantic_order_unique(
            self.module_release_ids,
            name="route module release ids",
        )
        for index, release_id in enumerate(release_ids):
            _require_root(release_id, name=f"route module release id[{index}]")
        roles = _require_semantic_order_unique(self.dependency_roles, name="route dependency roles")
        _require_tuple(self.port_schema_roots, name="route port schema roots")
        for index, root in enumerate(self.port_schema_roots):
            _require_root(root, name=f"route port schema root[{index}]")
        size = len(self.ordered_lanes)
        if len(release_ids) != size or len(roles) != size or len(self.port_schema_roots) != size:
            raise ValueError("route lanes, releases, roles, and port schemas must align exactly")
        for field_name in (
            "guest_image_id",
            "specification_root",
            "source_root",
            "toolchain_root",
        ):
            _require_root(getattr(self, field_name), name=f"route {field_name}")
        _require_root(self.oracle_policy_root, name="route oracle policy root")
        _require_root(self.issue_burn_policy_root, name="route issue/burn policy root")
        _require_positive_int(self.max_cycles, name="route max_cycles")
        _require_positive_int(self.max_journal_bytes, name="route max_journal_bytes")
        if self.max_cycles > MAX_CYCLE_BUDGET_V1:
            raise ValueError("route max_cycles exceeds ABI V1 ceiling")
        if self.max_journal_bytes > MAX_JOURNAL_BYTES_V1:
            raise ValueError("route max_journal_bytes exceeds ABI V1 ceiling")
        if type(self.status) is not ReleaseStatusV1:
            raise TypeError("route release status is not closed")
        _require_bool(self.accepts_new_objects, name="route accepts_new_objects")
        evidence = _evidence_tuple(self.evidence_statuses, name="route evidence statuses")
        if EvidenceStatusV1.DISABLED_PROVED_NO_WRITER in evidence:
            raise ValueError("DISABLED_PROVED_NO_WRITER is a lane-only evidence status")
        if self.accepts_new_objects and self.status is not ReleaseStatusV1.ACTIVE_NEW:
            raise ValueError("only ACTIVE_NEW routes may accept new objects")
        if self.status is ReleaseStatusV1.ACTIVE_NEW and not self.accepts_new_objects:
            raise ValueError("ACTIVE_NEW routes must accept new objects")
        if self.status is ReleaseStatusV1.ACTIVE_NEW and set(evidence) != REQUIRED_ACTIVE_EVIDENCE_V1:
            raise ValueError("ACTIVE_NEW route lacks the complete release evidence set")
        if self.route_release_id != self.derived_release_id:
            raise ValueError("route_release_id is not the exact content-derived id")

    @classmethod
    def build(
        cls,
        *,
        semantic_version: str,
        command_kind: str,
        ordered_lanes: tuple[LaneIdV1, ...],
        module_release_ids: tuple[str, ...],
        dependency_roles: tuple[str, ...],
        port_schema_roots: tuple[str, ...],
        guest_image_id: str,
        specification_root: str,
        source_root: str,
        toolchain_root: str,
        oracle_policy_root: str,
        issue_burn_policy_root: str,
        max_cycles: int,
        max_journal_bytes: int,
        status: ReleaseStatusV1,
        accepts_new_objects: bool,
        evidence_statuses: tuple[EvidenceStatusV1, ...] = (),
    ) -> RouteReleaseV1:
        if cls is not RouteReleaseV1:
            raise TypeError("route release factory requires the exact declared type")
        body = RouteReleaseV1._content_body(
            command_kind=command_kind,
            ordered_lanes=ordered_lanes,
            module_release_ids=module_release_ids,
            dependency_roles=dependency_roles,
            port_schema_roots=port_schema_roots,
            guest_image_id=guest_image_id,
            specification_root=specification_root,
            source_root=source_root,
            toolchain_root=toolchain_root,
            oracle_policy_root=oracle_policy_root,
            issue_burn_policy_root=issue_burn_policy_root,
            max_cycles=max_cycles,
            max_journal_bytes=max_journal_bytes,
        )
        return RouteReleaseV1(
            route_release_id=hash_global_v1("global-route-release-content-v1", body),
            semantic_version=semantic_version,
            command_kind=command_kind,
            ordered_lanes=ordered_lanes,
            module_release_ids=module_release_ids,
            dependency_roles=dependency_roles,
            port_schema_roots=port_schema_roots,
            guest_image_id=guest_image_id,
            specification_root=specification_root,
            source_root=source_root,
            toolchain_root=toolchain_root,
            oracle_policy_root=oracle_policy_root,
            issue_burn_policy_root=issue_burn_policy_root,
            max_cycles=max_cycles,
            max_journal_bytes=max_journal_bytes,
            status=status,
            accepts_new_objects=accepts_new_objects,
            evidence_statuses=evidence_statuses,
        )

    @staticmethod
    def _content_body(**values: object) -> dict[str, object]:
        return {"schema": GLOBAL_SETTLEMENT_ABI_V1, **values}

    @property
    def derived_release_id(self) -> str:
        return hash_global_v1(
            "global-route-release-content-v1",
            self._content_body(
                command_kind=self.command_kind,
                ordered_lanes=self.ordered_lanes,
                module_release_ids=self.module_release_ids,
                dependency_roles=self.dependency_roles,
                port_schema_roots=self.port_schema_roots,
                guest_image_id=self.guest_image_id,
                specification_root=self.specification_root,
                source_root=self.source_root,
                toolchain_root=self.toolchain_root,
                oracle_policy_root=self.oracle_policy_root,
                issue_burn_policy_root=self.issue_burn_policy_root,
                max_cycles=self.max_cycles,
                max_journal_bytes=self.max_journal_bytes,
            ),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            **self._content_body(
                command_kind=self.command_kind,
                ordered_lanes=self.ordered_lanes,
                module_release_ids=self.module_release_ids,
                dependency_roles=self.dependency_roles,
                port_schema_roots=self.port_schema_roots,
                guest_image_id=self.guest_image_id,
                specification_root=self.specification_root,
                source_root=self.source_root,
                toolchain_root=self.toolchain_root,
                oracle_policy_root=self.oracle_policy_root,
                issue_burn_policy_root=self.issue_burn_policy_root,
                max_cycles=self.max_cycles,
                max_journal_bytes=self.max_journal_bytes,
            ),
            "route_release_id": self.route_release_id,
            "semantic_version": self.semantic_version,
            "status": self.status,
            "accepts_new_objects": self.accepts_new_objects,
            "evidence_statuses": self.evidence_statuses,
        }


@dataclass(frozen=True, slots=True)
class RouteRegistryV1:
    routes: tuple[RouteReleaseV1, ...]

    def __post_init__(self) -> None:
        _require_tuple(self.routes, name="route registry routes")
        if any(type(item) is not RouteReleaseV1 for item in self.routes):
            raise TypeError("route registry contains an invalid release")
        keys = tuple(item.command_kind for item in self.routes)
        if keys != tuple(sorted(set(keys))):
            raise ValueError("route registry must be command-kind ordered and unique")

    @property
    def registry_root(self) -> str:
        return hash_global_v1("global-route-registry-v1", self.to_canonical())

    def route_for_command(
        self,
        command_kind: str,
        *,
        claimed_route_release_id: str | None = None,
    ) -> RouteReleaseV1:
        _require_token(command_kind, name="command kind")
        for route in self.routes:
            if route.command_kind != command_kind:
                continue
            if route.status is not ReleaseStatusV1.ACTIVE_NEW or not route.accepts_new_objects:
                raise ValueError("command route is disabled for new objects")
            if claimed_route_release_id is not None and claimed_route_release_id != route.route_release_id:
                raise ValueError("caller-selected route does not match governed route")
            return route
        raise ValueError("unknown or unregistered command kind")

    def to_canonical(self) -> dict[str, object]:
        return {"schema": GLOBAL_SETTLEMENT_ABI_V1, "routes": self.routes}


@dataclass(frozen=True, slots=True)
class EconomicPolicyBindingV1:
    policy_kind: str
    command_kind: str
    policy_root: str

    def __post_init__(self) -> None:
        _require_token(self.policy_kind, name="economic policy kind")
        _require_token(self.command_kind, name="economic policy command kind")
        _require_root(self.policy_root, name="economic policy root")

    def to_canonical(self) -> dict[str, object]:
        return {
            "policy_kind": self.policy_kind,
            "command_kind": self.command_kind,
            "policy_root": self.policy_root,
        }


@dataclass(frozen=True, slots=True)
class EconomicPolicyRegistryV1:
    bindings: tuple[EconomicPolicyBindingV1, ...]

    def __post_init__(self) -> None:
        _require_tuple(self.bindings, name="economic policy registry bindings")
        if len(self.bindings) > MAX_POLICY_BINDINGS_V1:
            raise ValueError("economic policy registry exceeds the ABI V1 bound")
        if any(type(binding) is not EconomicPolicyBindingV1 for binding in self.bindings):
            raise TypeError("economic policy registry contains an invalid binding")
        keys = tuple(
            (binding.policy_kind, binding.command_kind) for binding in self.bindings
        )
        if tuple(sorted(set(keys))) != keys:
            raise ValueError("economic policy registry must be sorted and unique")

    @property
    def registry_root(self) -> str:
        return hash_global_v1("global-economic-policy-registry-v1", self.to_canonical())

    def require_binding(
        self,
        *,
        policy_kind: str,
        command_kind: str,
    ) -> EconomicPolicyBindingV1:
        _require_token(policy_kind, name="economic policy kind")
        _require_token(command_kind, name="economic policy command kind")
        for binding in self.bindings:
            if (
                binding.policy_kind == policy_kind
                and binding.command_kind == command_kind
            ):
                return binding
        raise ValueError("economic policy binding is absent from the governed registry")

    def to_canonical(self) -> dict[str, object]:
        return {"schema": GLOBAL_SETTLEMENT_ABI_V1, "bindings": self.bindings}


@dataclass(frozen=True, slots=True)
class EconomicProfileSnapshotV1:
    profile_id: str
    authority_epoch: int
    lane_registry: LaneRegistryV1
    lane_coordinator_registry: LaneCoordinatorRegistryV1
    route_registry: RouteRegistryV1
    proof_shape_root: str
    root_image_id: str
    verifier_registry_root: str
    migration_registry_root: str
    policy_registry_root: str
    terminal_registry_root: str
    status: ProfileStatusV1

    def __post_init__(self) -> None:
        _require_root(self.profile_id, name="economic profile id")
        _require_nonnegative_int(self.authority_epoch, name="profile authority epoch")
        if type(self.lane_registry) is not LaneRegistryV1:
            raise TypeError("profile lane registry is invalid")
        if type(self.lane_coordinator_registry) is not LaneCoordinatorRegistryV1:
            raise TypeError("profile lane coordinator registry is invalid")
        if type(self.route_registry) is not RouteRegistryV1:
            raise TypeError("profile route registry is invalid")
        for field_name in (
            "proof_shape_root",
            "root_image_id",
            "verifier_registry_root",
            "migration_registry_root",
            "policy_registry_root",
            "terminal_registry_root",
        ):
            _require_root(getattr(self, field_name), name=f"profile {field_name}")
        if type(self.status) is not ProfileStatusV1:
            raise TypeError("profile status is not closed")
        if self.profile_id != self.derived_profile_id:
            raise ValueError("profile_id is not the exact content-derived id")
        self._validate_route_bindings()
        if self.status is ProfileStatusV1.ACTIVE:
            self._validate_activation_evidence()

    @classmethod
    def build(
        cls,
        *,
        authority_epoch: int,
        lane_registry: LaneRegistryV1,
        lane_coordinator_registry: LaneCoordinatorRegistryV1,
        route_registry: RouteRegistryV1,
        proof_shape_root: str,
        root_image_id: str,
        verifier_registry_root: str,
        migration_registry_root: str,
        policy_registry_root: str,
        terminal_registry_root: str,
        status: ProfileStatusV1,
    ) -> EconomicProfileSnapshotV1:
        if cls is not EconomicProfileSnapshotV1:
            raise TypeError("economic profile factory requires the exact declared type")
        body = EconomicProfileSnapshotV1._content_body(
            authority_epoch=authority_epoch,
            lane_registry_root=lane_registry.registry_root,
            lane_coordinator_registry_root=lane_coordinator_registry.registry_root,
            route_registry_root=route_registry.registry_root,
            proof_shape_root=proof_shape_root,
            root_image_id=root_image_id,
            verifier_registry_root=verifier_registry_root,
            migration_registry_root=migration_registry_root,
            policy_registry_root=policy_registry_root,
            terminal_registry_root=terminal_registry_root,
        )
        return EconomicProfileSnapshotV1(
            profile_id=hash_global_v1("global-economic-profile-content-v1", body),
            authority_epoch=authority_epoch,
            lane_registry=lane_registry,
            lane_coordinator_registry=lane_coordinator_registry,
            route_registry=route_registry,
            proof_shape_root=proof_shape_root,
            root_image_id=root_image_id,
            verifier_registry_root=verifier_registry_root,
            migration_registry_root=migration_registry_root,
            policy_registry_root=policy_registry_root,
            terminal_registry_root=terminal_registry_root,
            status=status,
        )

    @staticmethod
    def _content_body(**values: object) -> dict[str, object]:
        return {"schema": GLOBAL_SETTLEMENT_ABI_V1, **values}

    @property
    def derived_profile_id(self) -> str:
        return hash_global_v1(
            "global-economic-profile-content-v1",
            self._content_body(
                authority_epoch=self.authority_epoch,
                lane_registry_root=self.lane_registry.registry_root,
                lane_coordinator_registry_root=self.lane_coordinator_registry.registry_root,
                route_registry_root=self.route_registry.registry_root,
                proof_shape_root=self.proof_shape_root,
                root_image_id=self.root_image_id,
                verifier_registry_root=self.verifier_registry_root,
                migration_registry_root=self.migration_registry_root,
                policy_registry_root=self.policy_registry_root,
                terminal_registry_root=self.terminal_registry_root,
            ),
        )

    def _validate_route_bindings(self) -> None:
        for route in self.route_registry.routes:
            for lane_id, release_id in zip(
                route.ordered_lanes,
                route.module_release_ids,
                strict=True,
            ):
                lane_release = self.lane_registry.release_for(lane_id)
                coordinator_release = self.lane_coordinator_registry.release_for(lane_id)
                if lane_release.release_id != release_id:
                    raise ValueError("route module release does not match profile lane registry")
                if route.status is ReleaseStatusV1.ACTIVE_NEW and (
                    lane_release.status is not ReleaseStatusV1.ACTIVE_NEW
                    or not lane_release.accepts_new_objects
                ):
                    raise ValueError("active route references a lane release unavailable for new objects")
                if route.status is ReleaseStatusV1.ACTIVE_NEW and (
                    coordinator_release.status is not ReleaseStatusV1.ACTIVE_NEW
                    or not coordinator_release.accepts_new_objects
                ):
                    raise ValueError(
                        "active route references a lane coordinator unavailable for new objects"
                    )

    def _validate_activation_evidence(self) -> None:
        for release in self.lane_registry.releases:
            evidence = set(release.evidence_statuses)
            active = release.status is ReleaseStatusV1.ACTIVE_NEW and release.accepts_new_objects
            disabled = EvidenceStatusV1.DISABLED_PROVED_NO_WRITER in evidence
            if not active and not disabled:
                raise ValueError("active profile lane is neither release-backed nor proved disabled")
        for coordinator in self.lane_coordinator_registry.releases:
            evidence = set(coordinator.evidence_statuses)
            active = (
                coordinator.status is ReleaseStatusV1.ACTIVE_NEW
                and coordinator.accepts_new_objects
            )
            disabled = EvidenceStatusV1.DISABLED_PROVED_NO_WRITER in evidence
            if not active and not disabled:
                raise ValueError(
                    "active profile lane coordinator is neither release-backed nor proved disabled"
                )
        for route in self.route_registry.routes:
            if route.status is not ReleaseStatusV1.ACTIVE_NEW or not route.accepts_new_objects:
                raise ValueError("active profile contains a non-active route")

    def to_canonical(self) -> dict[str, object]:
        return {
            **self._content_body(
                authority_epoch=self.authority_epoch,
                lane_registry_root=self.lane_registry.registry_root,
                lane_coordinator_registry_root=self.lane_coordinator_registry.registry_root,
                route_registry_root=self.route_registry.registry_root,
                proof_shape_root=self.proof_shape_root,
                root_image_id=self.root_image_id,
                verifier_registry_root=self.verifier_registry_root,
                migration_registry_root=self.migration_registry_root,
                policy_registry_root=self.policy_registry_root,
                terminal_registry_root=self.terminal_registry_root,
            ),
            "profile_id": self.profile_id,
            "status": self.status,
        }


@dataclass(frozen=True, slots=True, order=True)
class LaneStateRootV1:
    lane_id: LaneIdV1
    module_release_id: str
    enabled: bool
    state_root: str

    def __post_init__(self) -> None:
        if type(self.lane_id) is not LaneIdV1:
            raise TypeError("lane state root lane_id is not closed")
        _require_root(self.module_release_id, name="lane state module release id")
        _require_bool(self.enabled, name="lane state enabled")
        _require_root(self.state_root, name="lane state root", allow_zero=True)

    def to_canonical(self) -> dict[str, object]:
        return {
            "lane_id": self.lane_id,
            "module_release_id": self.module_release_id,
            "enabled": self.enabled,
            "state_root": self.state_root,
        }


@dataclass(frozen=True, slots=True, order=True)
class EconomicAmountV1:
    owner: str
    asset: str
    custody_domain: str
    amount_atoms: int

    def __post_init__(self) -> None:
        _require_token(self.owner, name="economic amount owner")
        _require_token(self.asset, name="economic amount asset")
        _require_token(self.custody_domain, name="economic amount custody domain")
        _require_atoms_u128(self.amount_atoms, name="economic amount atoms")

    @property
    def key(self) -> tuple[str, str, str]:
        return (self.asset, self.owner, self.custody_domain)

    def to_canonical(self) -> dict[str, object]:
        return {
            "owner": self.owner,
            "asset": self.asset,
            "custody_domain": self.custody_domain,
            "amount_atoms": self.amount_atoms,
        }


@dataclass(frozen=True, slots=True, order=True)
class AssetSupplyV1:
    asset: str
    amount_atoms: int

    def __post_init__(self) -> None:
        _require_token(self.asset, name="supply asset")
        _require_atoms_u128(self.amount_atoms, name="supply atoms")

    def to_canonical(self) -> dict[str, object]:
        return {"asset": self.asset, "amount_atoms": self.amount_atoms}


@dataclass(frozen=True, slots=True, order=True)
class OracleOccurrenceStateV1:
    oracle_id: str
    occurrence_root: str
    observed_height: int
    finalized: bool

    def __post_init__(self) -> None:
        _require_token(self.oracle_id, name="oracle id")
        _require_root(self.occurrence_root, name="oracle occurrence root")
        _require_nonnegative_int(self.observed_height, name="oracle observed height")
        _require_bool(self.finalized, name="oracle finalized")

    def to_canonical(self) -> dict[str, object]:
        return {
            "oracle_id": self.oracle_id,
            "occurrence_root": self.occurrence_root,
            "observed_height": self.observed_height,
            "finalized": self.finalized,
        }


@dataclass(frozen=True, slots=True, order=True)
class ReplayStateV1:
    replay_id: str
    occurrence_id: str

    def __post_init__(self) -> None:
        _require_token(self.replay_id, name="replay id")
        _require_root(self.occurrence_id, name="replay occurrence id")

    def to_canonical(self) -> dict[str, object]:
        return {"replay_id": self.replay_id, "occurrence_id": self.occurrence_id}


class TerminalObligationStatusV1(str, Enum):
    OPEN = "OPEN"
    DRAINED = "DRAINED"
    TOMBSTONED = "TOMBSTONED"


@dataclass(frozen=True, slots=True, order=True)
class TerminalObligationV1:
    obligation_id: str
    lane_id: LaneIdV1
    claimant: str
    asset: str
    amount_atoms: int
    status: TerminalObligationStatusV1

    def __post_init__(self) -> None:
        _require_token(self.obligation_id, name="terminal obligation id")
        if type(self.lane_id) is not LaneIdV1:
            raise TypeError("terminal obligation lane is not closed")
        _require_token(self.claimant, name="terminal obligation claimant")
        _require_token(self.asset, name="terminal obligation asset")
        _require_atoms_u128(self.amount_atoms, name="terminal obligation amount")
        if type(self.status) is not TerminalObligationStatusV1:
            raise TypeError("terminal obligation status is not closed")

    def to_canonical(self) -> dict[str, object]:
        return {
            "obligation_id": self.obligation_id,
            "lane_id": self.lane_id,
            "claimant": self.claimant,
            "asset": self.asset,
            "amount_atoms": self.amount_atoms,
            "status": self.status,
        }


class OutboxStatusV1(str, Enum):
    PENDING = "PENDING"
    ACKNOWLEDGED = "ACKNOWLEDGED"


@dataclass(frozen=True, slots=True, order=True)
class OutboxStateV1:
    effect_id: str
    destination_id: str
    payload_hash: str
    commit_id: str
    status: OutboxStatusV1

    def __post_init__(self) -> None:
        _require_root(self.effect_id, name="outbox effect id")
        _require_token(self.destination_id, name="outbox destination id")
        _require_root(self.payload_hash, name="outbox payload hash")
        _require_root(self.commit_id, name="outbox commit id")
        if type(self.status) is not OutboxStatusV1:
            raise TypeError("outbox status is not closed")

    def to_canonical(self) -> dict[str, object]:
        return {
            "effect_id": self.effect_id,
            "destination_id": self.destination_id,
            "payload_hash": self.payload_hash,
            "commit_id": self.commit_id,
            "status": self.status,
        }


def _require_ordered_objects(
    values: object,
    *,
    name: str,
    expected_type: type[object],
    key: str,
) -> tuple[object, ...]:
    items = _require_tuple(values, name=name)
    if any(type(item) is not expected_type for item in items):
        raise TypeError(f"{name} contains an invalid value")
    keys = tuple(getattr(item, key) for item in items)
    if keys != tuple(sorted(set(keys))):
        raise ValueError(f"{name} must be canonically ordered and unique")
    return items


@dataclass(frozen=True, slots=True)
class GlobalEconomicStateV1:
    chain_id: str
    deployment_root: str
    writer_epoch: int
    height: int
    profile_root: str
    lane_roots: tuple[LaneStateRootV1, ...]
    balances: tuple[EconomicAmountV1, ...] = ()
    supplies: tuple[AssetSupplyV1, ...] = ()
    custody: tuple[EconomicAmountV1, ...] = ()
    liabilities: tuple[EconomicAmountV1, ...] = ()
    reserves: tuple[EconomicAmountV1, ...] = ()
    oracle_occurrences: tuple[OracleOccurrenceStateV1, ...] = ()
    replay_state: tuple[ReplayStateV1, ...] = ()
    terminal_obligations: tuple[TerminalObligationV1, ...] = ()
    history_root: str = ZERO_ROOT_V1
    outbox: tuple[OutboxStateV1, ...] = ()

    def __post_init__(self) -> None:
        _require_token(self.chain_id, name="global state chain id")
        _require_root(self.deployment_root, name="global state deployment root")
        _require_nonnegative_int(self.writer_epoch, name="global state writer epoch")
        _require_nonnegative_int(self.height, name="global state height")
        _require_root(self.profile_root, name="global state profile root")
        _require_tuple(self.lane_roots, name="global state lane roots")
        if any(type(item) is not LaneStateRootV1 for item in self.lane_roots):
            raise TypeError("global state contains an invalid lane root")
        if tuple(item.lane_id for item in self.lane_roots) != ALL_LANE_IDS_V1:
            raise ValueError("global state must commit every ABI V1 lane in canonical order")
        for field_name in ("balances", "custody", "liabilities", "reserves"):
            values = getattr(self, field_name)
            _require_ordered_objects(
                values,
                name=f"global state {field_name}",
                expected_type=EconomicAmountV1,
                key="key",
            )
        _require_ordered_objects(
            self.supplies,
            name="global state supplies",
            expected_type=AssetSupplyV1,
            key="asset",
        )
        _require_ordered_objects(
            self.oracle_occurrences,
            name="global state oracle occurrences",
            expected_type=OracleOccurrenceStateV1,
            key="oracle_id",
        )
        _require_ordered_objects(
            self.replay_state,
            name="global state replay state",
            expected_type=ReplayStateV1,
            key="replay_id",
        )
        replay_occurrence_ids = tuple(row.occurrence_id for row in self.replay_state)
        if len(replay_occurrence_ids) != len(set(replay_occurrence_ids)):
            raise ValueError("global state replay occurrence ids must be unique")
        _require_ordered_objects(
            self.terminal_obligations,
            name="global state terminal obligations",
            expected_type=TerminalObligationV1,
            key="obligation_id",
        )
        _require_root(self.history_root, name="global state history root", allow_zero=True)
        _require_ordered_objects(
            self.outbox,
            name="global state outbox",
            expected_type=OutboxStateV1,
            key="effect_id",
        )

    @property
    def state_root(self) -> str:
        return hash_global_v1("global-economic-state-root-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "chain_id": self.chain_id,
            "deployment_root": self.deployment_root,
            "writer_epoch": self.writer_epoch,
            "height": self.height,
            "profile_root": self.profile_root,
            "lane_roots": self.lane_roots,
            "balances": self.balances,
            "supplies": self.supplies,
            "custody": self.custody,
            "liabilities": self.liabilities,
            "reserves": self.reserves,
            "oracle_occurrences": self.oracle_occurrences,
            "replay_state": self.replay_state,
            "terminal_obligations": self.terminal_obligations,
            "history_root": self.history_root,
            "outbox": self.outbox,
        }


@dataclass(frozen=True, slots=True)
class GlobalEconomicStateRootV1:
    root: str
    profile_root: str
    writer_epoch: int
    height: int

    def __post_init__(self) -> None:
        _require_root(self.root, name="global economic state root")
        _require_root(self.profile_root, name="global economic state profile root")
        _require_nonnegative_int(self.writer_epoch, name="global economic state writer epoch")
        _require_nonnegative_int(self.height, name="global economic state height")

    @classmethod
    def from_state(cls, state: GlobalEconomicStateV1) -> GlobalEconomicStateRootV1:
        if cls is not GlobalEconomicStateRootV1:
            raise TypeError("state root factory requires the exact declared type")
        if type(state) is not GlobalEconomicStateV1:
            raise TypeError("state root source must be GlobalEconomicStateV1")
        return GlobalEconomicStateRootV1(
            state.state_root,
            state.profile_root,
            state.writer_epoch,
            state.height,
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "root": self.root,
            "profile_root": self.profile_root,
            "writer_epoch": self.writer_epoch,
            "height": self.height,
        }


def validate_global_state_profile_v1(
    state: GlobalEconomicStateV1,
    profile: EconomicProfileSnapshotV1,
) -> None:
    """Reject state/profile drift at verifier and publication boundaries."""

    if type(state) is not GlobalEconomicStateV1:
        raise TypeError("state must be GlobalEconomicStateV1")
    if type(profile) is not EconomicProfileSnapshotV1:
        raise TypeError("profile must be EconomicProfileSnapshotV1")
    if state.profile_root != profile.profile_id:
        raise ValueError("global state profile root mismatch")
    if state.writer_epoch != profile.authority_epoch:
        raise ValueError("global state writer epoch mismatch")
    for lane_state, release in zip(state.lane_roots, profile.lane_registry.releases, strict=True):
        if lane_state.lane_id is not release.lane_id:
            raise ValueError("global state lane order mismatch")
        if lane_state.module_release_id != release.release_id:
            raise ValueError("global state lane release mismatch")
        expected_enabled = (
            release.status is ReleaseStatusV1.ACTIVE_NEW and release.accepts_new_objects
        )
        if lane_state.enabled is not expected_enabled:
            raise ValueError("global state lane enabled flag does not match release status")


class EconomicEffectKindV1(str, Enum):
    ACCOUNT_MOVEMENT = "ACCOUNT_MOVEMENT"
    ISSUE = "ISSUE"
    BURN = "BURN"
    CUSTODY = "CUSTODY"
    LIABILITY = "LIABILITY"
    RESERVE = "RESERVE"
    FEE_ALLOCATION = "FEE_ALLOCATION"
    REWARD = "REWARD"
    SLASH = "SLASH"


@dataclass(frozen=True, slots=True, order=True)
class EconomicEffectRowV1:
    kind: EconomicEffectKindV1
    principal: str
    asset: str
    custody_domain: str
    delta_atoms: int

    def __post_init__(self) -> None:
        if type(self.kind) is not EconomicEffectKindV1:
            raise TypeError("economic effect kind is not closed")
        _require_token(self.principal, name="economic effect principal")
        _require_token(self.asset, name="economic effect asset")
        _require_token(self.custody_domain, name="economic effect custody domain")
        _require_delta_atoms_i128(self.delta_atoms, name="economic effect delta")
        if self.delta_atoms == 0:
            raise ValueError("economic effect delta must be nonzero")
        if self.kind is EconomicEffectKindV1.ISSUE and self.delta_atoms < 0:
            raise ValueError("issue effect must be positive")
        if self.kind is EconomicEffectKindV1.BURN and self.delta_atoms > 0:
            raise ValueError("burn effect must be negative")

    @property
    def key(self) -> tuple[str, str, str, str]:
        return (self.kind.value, self.asset, self.principal, self.custody_domain)

    def to_canonical(self) -> dict[str, object]:
        return {
            "kind": self.kind,
            "principal": self.principal,
            "asset": self.asset,
            "custody_domain": self.custody_domain,
            "delta_atoms": self.delta_atoms,
        }


@dataclass(frozen=True, slots=True, order=True)
class AssetConservationRowV1:
    asset: str
    owned_and_custodied_pre_atoms: int
    owned_and_custodied_post_atoms: int
    supply_pre_atoms: int
    supply_post_atoms: int
    authorized_issue_atoms: int
    authorized_burn_atoms: int

    def __post_init__(self) -> None:
        _require_token(self.asset, name="conservation asset")
        for field_name in (
            "owned_and_custodied_pre_atoms",
            "owned_and_custodied_post_atoms",
            "supply_pre_atoms",
            "supply_post_atoms",
            "authorized_issue_atoms",
            "authorized_burn_atoms",
        ):
            _require_atoms_u128(getattr(self, field_name), name=f"conservation {field_name}")
        expected_owned = (
            self.owned_and_custodied_pre_atoms
            + self.authorized_issue_atoms
            - self.authorized_burn_atoms
        )
        expected_supply = self.supply_pre_atoms + self.authorized_issue_atoms - self.authorized_burn_atoms
        if expected_owned < 0 or self.owned_and_custodied_post_atoms != expected_owned:
            raise ValueError("owned-and-custodied conservation mismatch")
        if expected_supply < 0 or self.supply_post_atoms != expected_supply:
            raise ValueError("supply conservation mismatch")

    def to_canonical(self) -> dict[str, object]:
        return {
            "asset": self.asset,
            "owned_and_custodied_pre_atoms": self.owned_and_custodied_pre_atoms,
            "owned_and_custodied_post_atoms": self.owned_and_custodied_post_atoms,
            "supply_pre_atoms": self.supply_pre_atoms,
            "supply_post_atoms": self.supply_post_atoms,
            "authorized_issue_atoms": self.authorized_issue_atoms,
            "authorized_burn_atoms": self.authorized_burn_atoms,
        }


@dataclass(frozen=True, slots=True, order=True)
class FeeConservationRowV1:
    asset: str
    fee_charged_atoms: int
    current_allocations_atoms: int
    carried_residue_atoms: int

    def __post_init__(self) -> None:
        _require_token(self.asset, name="fee conservation asset")
        for field_name in (
            "fee_charged_atoms",
            "current_allocations_atoms",
            "carried_residue_atoms",
        ):
            _require_atoms_u128(getattr(self, field_name), name=f"fee conservation {field_name}")
        if self.fee_charged_atoms != self.current_allocations_atoms + self.carried_residue_atoms:
            raise ValueError("fee allocation and carried residue do not reconcile")

    def to_canonical(self) -> dict[str, object]:
        return {
            "asset": self.asset,
            "fee_charged_atoms": self.fee_charged_atoms,
            "current_allocations_atoms": self.current_allocations_atoms,
            "carried_residue_atoms": self.carried_residue_atoms,
        }


@dataclass(frozen=True, slots=True, order=True)
class LaneWriteV1:
    lane_id: LaneIdV1
    pre_root: str
    post_root: str

    def __post_init__(self) -> None:
        if type(self.lane_id) is not LaneIdV1:
            raise TypeError("lane write lane is not closed")
        _require_root(self.pre_root, name="lane write pre-root", allow_zero=True)
        _require_root(self.post_root, name="lane write post-root", allow_zero=True)

    def to_canonical(self) -> dict[str, object]:
        return {"lane_id": self.lane_id, "pre_root": self.pre_root, "post_root": self.post_root}


@dataclass(frozen=True, slots=True, order=True)
class ExternalOutboxEnqueueV1:
    effect_id: str
    destination_id: str
    payload_hash: str
    adapter_profile_root: str

    def __post_init__(self) -> None:
        _require_root(self.effect_id, name="external outbox effect id")
        _require_token(self.destination_id, name="external outbox destination")
        if self.destination_id.startswith("zenoledger:"):
            raise ValueError("same-ledger movement must not enter the external outbox")
        _require_root(self.payload_hash, name="external outbox payload hash")
        _require_root(self.adapter_profile_root, name="external outbox adapter profile root")

    def to_canonical(self) -> dict[str, object]:
        return {
            "effect_id": self.effect_id,
            "destination_id": self.destination_id,
            "payload_hash": self.payload_hash,
            "adapter_profile_root": self.adapter_profile_root,
        }


@dataclass(frozen=True, slots=True)
class GlobalEconomicEffectPlanV1:
    rows: tuple[EconomicEffectRowV1, ...]
    asset_conservation: tuple[AssetConservationRowV1, ...]
    fee_conservation: tuple[FeeConservationRowV1, ...]
    lane_writes: tuple[LaneWriteV1, ...]
    occurrence_consumptions: tuple[str, ...]
    external_outbox_enqueue: tuple[ExternalOutboxEnqueueV1, ...]

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        _require_ordered_objects(
            self.rows,
            name="effect plan rows",
            expected_type=EconomicEffectRowV1,
            key="key",
        )
        _require_ordered_objects(
            self.asset_conservation,
            name="effect plan asset conservation",
            expected_type=AssetConservationRowV1,
            key="asset",
        )
        _require_ordered_objects(
            self.fee_conservation,
            name="effect plan fee conservation",
            expected_type=FeeConservationRowV1,
            key="asset",
        )
        _require_ordered_objects(
            self.lane_writes,
            name="effect plan lane writes",
            expected_type=LaneWriteV1,
            key="lane_id",
        )
        consumptions = _require_sorted_unique_tokens(
            self.occurrence_consumptions,
            name="effect plan occurrence consumptions",
        )
        for index, occurrence_id in enumerate(consumptions):
            _require_root(occurrence_id, name=f"effect plan occurrence consumption[{index}]")
        _require_ordered_objects(
            self.external_outbox_enqueue,
            name="effect plan external outbox",
            expected_type=ExternalOutboxEnqueueV1,
            key="effect_id",
        )
        self._validate_issue_burn_projection()
        self._validate_fee_projection()

    def _validate_issue_burn_projection(self) -> None:
        issue_by_asset: dict[str, int] = {}
        burn_by_asset: dict[str, int] = {}
        for row in self.rows:
            if row.kind is EconomicEffectKindV1.ISSUE:
                issue_by_asset[row.asset] = issue_by_asset.get(row.asset, 0) + row.delta_atoms
            elif row.kind is EconomicEffectKindV1.BURN:
                burn_by_asset[row.asset] = burn_by_asset.get(row.asset, 0) - row.delta_atoms
        conservation_assets = {row.asset for row in self.asset_conservation}
        effect_assets = set(issue_by_asset) | set(burn_by_asset)
        if not effect_assets.issubset(conservation_assets):
            raise ValueError("issue or burn effect lacks an asset conservation row")
        for conservation_row in self.asset_conservation:
            if conservation_row.authorized_issue_atoms != issue_by_asset.get(conservation_row.asset, 0):
                raise ValueError("authorized issue does not match canonical effect rows")
            if conservation_row.authorized_burn_atoms != burn_by_asset.get(conservation_row.asset, 0):
                raise ValueError("authorized burn does not match canonical effect rows")

    def _validate_fee_projection(self) -> None:
        allocations: dict[str, int] = {}
        for row in self.rows:
            if row.kind is EconomicEffectKindV1.FEE_ALLOCATION:
                if row.delta_atoms < 0:
                    raise ValueError("fee allocation effect must be positive")
                allocations[row.asset] = allocations.get(row.asset, 0) + row.delta_atoms
        for fee_row in self.fee_conservation:
            if fee_row.current_allocations_atoms != allocations.get(fee_row.asset, 0):
                raise ValueError("fee conservation does not match canonical allocation effects")
        if not set(allocations).issubset({row.asset for row in self.fee_conservation}):
            raise ValueError("fee allocation effect lacks a fee conservation row")

    @property
    def effect_plan_root(self) -> str:
        self.validate()
        return hash_global_v1("global-economic-effect-plan-v1", self.to_canonical())

    @property
    def is_empty(self) -> bool:
        return not (
            self.rows
            or self.asset_conservation
            or self.fee_conservation
            or self.lane_writes
            or self.occurrence_consumptions
            or self.external_outbox_enqueue
        )

    @classmethod
    def empty(cls) -> GlobalEconomicEffectPlanV1:
        if cls is not GlobalEconomicEffectPlanV1:
            raise TypeError("effect plan factory requires the exact declared type")
        return GlobalEconomicEffectPlanV1((), (), (), (), (), ())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "rows": self.rows,
            "asset_conservation": self.asset_conservation,
            "fee_conservation": self.fee_conservation,
            "lane_writes": self.lane_writes,
            "occurrence_consumptions": self.occurrence_consumptions,
            "external_outbox_enqueue": self.external_outbox_enqueue,
        }


class LaneTransitionRejectCodeV1(str, Enum):
    UNKNOWN_COMMAND = "UNKNOWN_COMMAND"
    DISABLED_FEATURE = "DISABLED_FEATURE"
    RELEASE_MISMATCH = "RELEASE_MISMATCH"
    INVALID_CONTEXT = "INVALID_CONTEXT"
    INVALID_STATE = "INVALID_STATE"
    POLICY_REJECT = "POLICY_REJECT"
    RESOURCE_LIMIT = "RESOURCE_LIMIT"


@dataclass(frozen=True, slots=True)
class LaneTransitionAcceptedV1:
    command_occurrence_id: str
    pre_state_root: str
    post_state_root: str
    effects: GlobalEconomicEffectPlanV1
    private_ports_root: str
    receipt_root: str
    terminal_obligations: tuple[TerminalObligationV1, ...]

    def __post_init__(self) -> None:
        for field_name in (
            "command_occurrence_id",
            "pre_state_root",
            "post_state_root",
            "private_ports_root",
            "receipt_root",
        ):
            _require_root(
                getattr(self, field_name),
                name=f"accepted transition {field_name}",
                allow_zero=field_name == "private_ports_root",
            )
        if type(self.effects) is not GlobalEconomicEffectPlanV1:
            raise TypeError("accepted transition effects are invalid")
        _require_ordered_objects(
            self.terminal_obligations,
            name="accepted transition terminal obligations",
            expected_type=TerminalObligationV1,
            key="obligation_id",
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "command_occurrence_id": self.command_occurrence_id,
            "pre_state_root": self.pre_state_root,
            "post_state_root": self.post_state_root,
            "effects": self.effects,
            "private_ports_root": self.private_ports_root,
            "receipt_root": self.receipt_root,
            "terminal_obligations": self.terminal_obligations,
        }


@dataclass(frozen=True, slots=True)
class LaneTransitionRejectedV1:
    code: LaneTransitionRejectCodeV1
    pre_state_root: str
    post_state_root: str
    effects: GlobalEconomicEffectPlanV1

    def __post_init__(self) -> None:
        if type(self.code) is not LaneTransitionRejectCodeV1:
            raise TypeError("lane transition reject code is not closed")
        _require_root(self.pre_state_root, name="rejected transition pre-state root")
        _require_root(self.post_state_root, name="rejected transition post-state root")
        if self.pre_state_root != self.post_state_root:
            raise ValueError("rejected transition must preserve the exact pre-state root")
        if type(self.effects) is not GlobalEconomicEffectPlanV1 or not self.effects.is_empty:
            raise ValueError("rejected transition must carry the empty effect plan")

    @classmethod
    def reject(
        cls,
        code: LaneTransitionRejectCodeV1,
        pre_state_root: str,
    ) -> LaneTransitionRejectedV1:
        if cls is not LaneTransitionRejectedV1:
            raise TypeError("lane rejection factory requires the exact declared type")
        return LaneTransitionRejectedV1(
            code,
            pre_state_root,
            pre_state_root,
            GlobalEconomicEffectPlanV1.empty(),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "code": self.code,
            "pre_state_root": self.pre_state_root,
            "post_state_root": self.post_state_root,
            "effects": self.effects,
        }


__all__ = [
    "GLOBAL_SETTLEMENT_ABI_V1",
    "MAX_ROUTE_MODULES_V1",
    "MAX_EPOCH_COMMANDS_V1",
    "MAX_EPOCH_LEAF_OCCURRENCES_V1",
    "MAX_POLICY_BINDINGS_V1",
    "MAX_JOURNAL_BYTES_V1",
    "MAX_CYCLE_BUDGET_V1",
    "MAX_U64_V1",
    "MAX_ATOMS_V1",
    "MIN_DELTA_ATOMS_V1",
    "MAX_DELTA_ATOMS_V1",
    "ZERO_ROOT_V1",
    "LaneIdV1",
    "ALL_LANE_IDS_V1",
    "ReleaseStatusV1",
    "EvidenceStatusV1",
    "REQUIRED_ACTIVE_EVIDENCE_V1",
    "ProfileStatusV1",
    "LaneModuleReleaseV1",
    "LaneRegistryV1",
    "LaneCoordinatorReleaseV1",
    "LaneCoordinatorRegistryV1",
    "RouteReleaseV1",
    "RouteRegistryV1",
    "EconomicPolicyBindingV1",
    "EconomicPolicyRegistryV1",
    "EconomicProfileSnapshotV1",
    "LaneStateRootV1",
    "EconomicAmountV1",
    "AssetSupplyV1",
    "OracleOccurrenceStateV1",
    "ReplayStateV1",
    "TerminalObligationStatusV1",
    "TerminalObligationV1",
    "OutboxStatusV1",
    "OutboxStateV1",
    "GlobalEconomicStateV1",
    "GlobalEconomicStateRootV1",
    "validate_global_state_profile_v1",
    "hash_economic_command_body_v1",
    "EconomicEffectKindV1",
    "EconomicEffectRowV1",
    "AssetConservationRowV1",
    "FeeConservationRowV1",
    "LaneWriteV1",
    "ExternalOutboxEnqueueV1",
    "GlobalEconomicEffectPlanV1",
    "LaneTransitionRejectCodeV1",
    "LaneTransitionAcceptedV1",
    "LaneTransitionRejectedV1",
    "canonical_global_bytes_v1",
    "canonical_economic_command_body_bytes_v1",
    "hash_economic_command_body_bytes_v1",
    "hash_global_v1",
]
