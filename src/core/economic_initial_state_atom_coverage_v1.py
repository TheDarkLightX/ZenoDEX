"""Canonical source classification for explicit initial-state value rows.

This deterministic core covers the value-bearing rows represented directly by
``GlobalEconomicStateV1``.  It does not inspect value hidden behind lane roots,
prove migration source-state totality, or verify the RISC0 receipt that commits
the resulting manifest root.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from typing import Final

from .global_economic_refinement_snapshot_v1 import _snapshot_state_v1
from .global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    AssetSupplyV1,
    EconomicAmountV1,
    EconomicPolicyBindingV1,
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    GlobalEconomicStateV1,
    TerminalObligationV1,
    _require_root,
    hash_global_v1,
)

MAX_INITIAL_STATE_ATOM_ROWS_V1: Final = 4_096
M6_INITIAL_STATE_ATOM_COVERAGE_POLICY_KIND_V1: Final = (
    "m6_initial_state_atom_coverage_v1"
)
M6_INITIAL_STATE_ATOM_COVERAGE_PROFILE_COMMAND_KIND_V1: Final = (
    "global_economic_profile_v1"
)


class EconomicInitialStateKindV1(str, Enum):
    GENESIS = "GENESIS"
    MIGRATION = "MIGRATION"


class EconomicInitialStateAtomKindV1(str, Enum):
    BALANCE = "BALANCE"
    SUPPLY = "SUPPLY"
    CUSTODY = "CUSTODY"
    LIABILITY = "LIABILITY"
    RESERVE = "RESERVE"
    TERMINAL_OBLIGATION = "TERMINAL_OBLIGATION"


class EconomicInitialStateAtomClassificationV1(str, Enum):
    GENESIS_ALLOCATION = "GENESIS_ALLOCATION"
    MIGRATED_TARGET = "MIGRATED_TARGET"
    RETAINED_DRAIN_TARGET = "RETAINED_DRAIN_TARGET"


_ATOM_KIND_ORDER_V1: Final = tuple(EconomicInitialStateAtomKindV1)
_ATOM_FIELDS_V1: Final = (
    (EconomicInitialStateAtomKindV1.BALANCE, "balances", EconomicAmountV1),
    (EconomicInitialStateAtomKindV1.SUPPLY, "supplies", AssetSupplyV1),
    (EconomicInitialStateAtomKindV1.CUSTODY, "custody", EconomicAmountV1),
    (EconomicInitialStateAtomKindV1.LIABILITY, "liabilities", EconomicAmountV1),
    (EconomicInitialStateAtomKindV1.RESERVE, "reserves", EconomicAmountV1),
    (
        EconomicInitialStateAtomKindV1.TERMINAL_OBLIGATION,
        "terminal_obligations",
        TerminalObligationV1,
    ),
)
_ALLOWED_CLASSIFICATIONS_V1: Final = {
    EconomicInitialStateKindV1.GENESIS: frozenset(
        {EconomicInitialStateAtomClassificationV1.GENESIS_ALLOCATION}
    ),
    EconomicInitialStateKindV1.MIGRATION: frozenset(
        {
            EconomicInitialStateAtomClassificationV1.MIGRATED_TARGET,
            EconomicInitialStateAtomClassificationV1.RETAINED_DRAIN_TARGET,
        }
    ),
}


def _require_exact_u64_v1(value: object, *, name: str) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an exact integer")
    if not 0 <= value <= (1 << 64) - 1:
        raise ValueError(f"{name} must fit an unsigned 64-bit integer")
    return value


def _expected_row_type_v1(atom_kind: EconomicInitialStateAtomKindV1) -> type[object]:
    for candidate_kind, _, expected_type in _ATOM_FIELDS_V1:
        if atom_kind is candidate_kind:
            return expected_type
    raise TypeError("initial state atom kind is not closed")


def _occurrence_order_key_v1(
    occurrence: EconomicInitialStateAtomOccurrenceV1,
) -> tuple[int, int]:
    return (_ATOM_KIND_ORDER_V1.index(occurrence.atom_kind), occurrence.state_row_index)


@dataclass(frozen=True, slots=True, order=True)
class EconomicInitialStateAtomOccurrenceV1:
    atom_kind: EconomicInitialStateAtomKindV1
    state_row_index: int
    row_root: str

    def __post_init__(self) -> None:
        if type(self.atom_kind) is not EconomicInitialStateAtomKindV1:
            raise TypeError("initial state atom kind is not closed")
        _require_exact_u64_v1(
            self.state_row_index,
            name="initial state atom row index",
        )
        if type(self.row_root) is not str:
            raise TypeError("initial state atom row root must be exact str")
        _require_root(self.row_root, name="initial state atom row root")

    def to_canonical(self) -> dict[str, object]:
        return {
            "atom_kind": self.atom_kind,
            "state_row_index": self.state_row_index,
            "row_root": self.row_root,
        }


def economic_initial_state_atom_occurrence_v1(
    atom_kind: EconomicInitialStateAtomKindV1,
    state_row_index: int,
    row: object,
) -> EconomicInitialStateAtomOccurrenceV1:
    """Derive one occurrence from a typed row and its canonical table index."""

    if type(atom_kind) is not EconomicInitialStateAtomKindV1:
        raise TypeError("initial state atom kind is not closed")
    _require_exact_u64_v1(state_row_index, name="initial state atom row index")
    expected_type = _expected_row_type_v1(atom_kind)
    if type(row) is not expected_type:
        raise TypeError("initial state atom row type does not match its kind")
    row_root = hash_global_v1(
        "economic-initial-state-atom-row-v1",
        {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "atom_kind": atom_kind,
            "state_row_index": state_row_index,
            "row": row,
        },
    )
    return EconomicInitialStateAtomOccurrenceV1(atom_kind, state_row_index, row_root)


@dataclass(frozen=True, slots=True)
class EconomicInitialStateAtomSourceV1:
    occurrence: EconomicInitialStateAtomOccurrenceV1
    classification: EconomicInitialStateAtomClassificationV1
    source_authorization_root: str

    def __post_init__(self) -> None:
        if type(self.occurrence) is not EconomicInitialStateAtomOccurrenceV1:
            raise TypeError("initial state atom occurrence type is not closed")
        if type(self.classification) is not EconomicInitialStateAtomClassificationV1:
            raise TypeError("initial state atom classification is not closed")
        if type(self.source_authorization_root) is not str:
            raise TypeError("initial state atom source authorization root must be exact str")
        _require_root(
            self.source_authorization_root,
            name="initial state atom source authorization root",
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "occurrence": self.occurrence,
            "classification": self.classification,
            "source_authorization_root": self.source_authorization_root,
        }


@dataclass(frozen=True, slots=True)
class EconomicInitialStateSourceManifestV1:
    kind: EconomicInitialStateKindV1
    rows: tuple[EconomicInitialStateAtomSourceV1, ...]

    def __post_init__(self) -> None:
        if type(self.kind) is not EconomicInitialStateKindV1:
            raise TypeError("initial state source manifest kind is not closed")
        if type(self.rows) is not tuple:
            raise TypeError("initial state source manifest rows must be a tuple")
        if len(self.rows) > MAX_INITIAL_STATE_ATOM_ROWS_V1:
            raise ValueError("initial state source manifest exceeds the row bound")
        if any(type(row) is not EconomicInitialStateAtomSourceV1 for row in self.rows):
            raise TypeError("initial state source manifest contains an invalid row")
        keys = tuple(_occurrence_order_key_v1(row.occurrence) for row in self.rows)
        if keys != tuple(sorted(set(keys))):
            raise ValueError("initial state source manifest rows must be ordered and unique")
        allowed = _ALLOWED_CLASSIFICATIONS_V1[self.kind]
        if any(row.classification not in allowed for row in self.rows):
            label = (
                "genesis allocation"
                if self.kind is EconomicInitialStateKindV1.GENESIS
                else "migration target"
            )
            raise ValueError(f"initial state source manifest has an invalid {label} classification")

    @property
    def manifest_root(self) -> str:
        return hash_global_v1(
            "economic-initial-state-atom-coverage-v1",
            self.to_canonical(),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "kind": self.kind,
            "rows": self.rows,
        }


def derive_economic_initial_state_atom_occurrences_v1(
    state: GlobalEconomicStateV1,
) -> tuple[EconomicInitialStateAtomOccurrenceV1, ...]:
    """Project every explicit value-bearing global-state row in ABI order."""

    if type(state) is not GlobalEconomicStateV1:
        raise TypeError("initial state atom coverage state type is not closed")
    total_rows = 0
    for _, field_name, _ in _ATOM_FIELDS_V1:
        rows = getattr(state, field_name)
        if type(rows) is not tuple:
            raise TypeError(f"initial state {field_name} rows must be an exact tuple")
        total_rows += len(rows)
        if total_rows > MAX_INITIAL_STATE_ATOM_ROWS_V1:
            raise ValueError("initial state explicit value rows exceed the coverage bound")
    owned_state = _snapshot_state_v1(state)
    occurrences: list[EconomicInitialStateAtomOccurrenceV1] = []
    for atom_kind, field_name, _ in _ATOM_FIELDS_V1:
        rows = getattr(owned_state, field_name)
        for state_row_index, row in enumerate(rows):
            occurrences.append(
                economic_initial_state_atom_occurrence_v1(
                    atom_kind,
                    state_row_index,
                    row,
                )
            )
    return tuple(occurrences)


def snapshot_economic_initial_state_source_manifest_v1(
    manifest: EconomicInitialStateSourceManifestV1,
) -> EconomicInitialStateSourceManifestV1:
    """Own and revalidate the complete manifest graph before callbacks."""

    if type(manifest) is not EconomicInitialStateSourceManifestV1:
        raise TypeError("initial state source manifest type is not closed")
    return EconomicInitialStateSourceManifestV1(
        manifest.kind,
        tuple(
            EconomicInitialStateAtomSourceV1(
                replace(row.occurrence),
                row.classification,
                row.source_authorization_root,
            )
            for row in manifest.rows
        ),
    )


def validate_economic_initial_state_atom_coverage_v1(
    state: GlobalEconomicStateV1,
    source_manifest: EconomicInitialStateSourceManifestV1,
) -> str:
    """Require one exact source classification for every explicit value row."""

    owned_manifest = snapshot_economic_initial_state_source_manifest_v1(source_manifest)
    expected_occurrences = derive_economic_initial_state_atom_occurrences_v1(state)
    actual_occurrences = tuple(row.occurrence for row in owned_manifest.rows)
    if actual_occurrences != expected_occurrences:
        raise ValueError("initial state atom manifest does not classify the exact target state")
    return owned_manifest.manifest_root


def economic_initial_state_atom_coverage_policy_binding_v1(
    source_manifest: EconomicInitialStateSourceManifestV1,
) -> EconomicPolicyBindingV1:
    owned_manifest = snapshot_economic_initial_state_source_manifest_v1(source_manifest)
    return EconomicPolicyBindingV1(
        policy_kind=M6_INITIAL_STATE_ATOM_COVERAGE_POLICY_KIND_V1,
        command_kind=M6_INITIAL_STATE_ATOM_COVERAGE_PROFILE_COMMAND_KIND_V1,
        policy_root=owned_manifest.manifest_root,
    )


def validate_economic_initial_state_atom_coverage_profile_binding_v1(
    profile: EconomicProfileSnapshotV1,
    policy_registry: EconomicPolicyRegistryV1,
    source_manifest: EconomicInitialStateSourceManifestV1,
) -> None:
    """Bind the exact source-classification manifest through the active profile."""

    if type(profile) is not EconomicProfileSnapshotV1:
        raise TypeError("initial state coverage profile type is not closed")
    if type(policy_registry) is not EconomicPolicyRegistryV1:
        raise TypeError("initial state coverage policy registry type is not closed")
    owned_manifest = snapshot_economic_initial_state_source_manifest_v1(source_manifest)
    if policy_registry.registry_root != profile.policy_registry_root:
        raise ValueError("initial state coverage policy registry root mismatch")
    binding = policy_registry.require_binding(
        policy_kind=M6_INITIAL_STATE_ATOM_COVERAGE_POLICY_KIND_V1,
        command_kind=M6_INITIAL_STATE_ATOM_COVERAGE_PROFILE_COMMAND_KIND_V1,
    )
    if binding.policy_root != owned_manifest.manifest_root:
        raise ValueError("initial state atom coverage manifest root mismatch")


__all__ = [
    "MAX_INITIAL_STATE_ATOM_ROWS_V1",
    "M6_INITIAL_STATE_ATOM_COVERAGE_POLICY_KIND_V1",
    "M6_INITIAL_STATE_ATOM_COVERAGE_PROFILE_COMMAND_KIND_V1",
    "EconomicInitialStateKindV1",
    "EconomicInitialStateAtomKindV1",
    "EconomicInitialStateAtomClassificationV1",
    "EconomicInitialStateAtomOccurrenceV1",
    "EconomicInitialStateAtomSourceV1",
    "EconomicInitialStateSourceManifestV1",
    "economic_initial_state_atom_occurrence_v1",
    "derive_economic_initial_state_atom_occurrences_v1",
    "snapshot_economic_initial_state_source_manifest_v1",
    "validate_economic_initial_state_atom_coverage_v1",
    "economic_initial_state_atom_coverage_policy_binding_v1",
    "validate_economic_initial_state_atom_coverage_profile_binding_v1",
]
