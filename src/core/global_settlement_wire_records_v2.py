"""Strict, wire-only records for previously unencoded V2 result surfaces.

These records describe exact canonical field sets without adding a schema tag,
hash domain, verifier, or authority.  They are deliberately separate from the
opaque accepted domain values: only context and candidate records can become
ordinary functional-core inputs.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Final, TypeAlias, cast

from .asset_lane_coordinator_values_v2 import (
    AssetLaneAcceptedV2,
    AssetLaneCoordinatorRejectCodeV2,
    AssetLaneRejectCodeV2,
    AssetLaneRejectedV2,
    AssetLaneRouteV2,
)
from .asset_lane_state_v2 import (
    ASSET_LANE_PROFILE_AUTHENTICATION_V2,
    AssetLaneContextV2,
    AssetLaneStateV2,
    _policy_origin_bindings_hold_v2,
    _snapshot_asset_lane_state_v2,
)
from .asset_origin_registry_types_v2 import (
    AssetOriginRegistrationAcceptedV2,
    AssetOriginRegistrationRejectCodeV2,
    AssetOriginRegistrationRejectedV2,
    AssetOriginRegistryStateV2,
    _snapshot_registry_state_v2,
)
from .asset_transfer_types_v2 import AssetTransferRejectCodeV2
from .global_economic_proof_v2 import (
    EconomicCommandOccurrenceV2,
    LaneModuleTransitionJournalV2,
    _snapshot_module_journal_v2,
    _snapshot_occurrence_v2,
)
from .global_economic_refinement_outcome_v2 import (
    GlobalEconomicRefinementAcceptedV2,
    GlobalEconomicRefinementRejectCodeV2,
    GlobalEconomicRefinementRejectedV2,
)
from .global_economic_state_effect_refinement_v2 import (
    GLOBAL_ECONOMIC_STATE_EFFECT_REFINEMENT_SCHEMA_V2,
    GlobalEconomicStateEffectRefinementCandidateV2,
    GlobalEconomicStateEffectRefinementV2,
)
from .global_economic_state_v2 import (
    GlobalEconomicStateV2,
    snapshot_global_economic_state_v2,
)
from .global_settlement_resource_limits_v2 import (
    MAX_CONSUMED_OCCURRENCES_PER_REFINEMENT_V2,
    require_raw_tuple_ceiling_v2,
)
from .global_settlement_types_v2 import (
    ZERO_ROOT_V2,
    ExternalOutboxEnqueueV2,
    GlobalEconomicEffectPlanV2,
    GlobalOracleOccurrencePlanV2,
    GlobalTerminalObligationPlanV2,
    LaneIdV2,
    LaneWriteV2,
    _require_root_v2,
    hash_global_v2,
)
from .managed_asset_lifecycle_types_v2 import (
    ManagedAssetLifecycleAcceptedV2,
    ManagedAssetLifecycleRejectCodeV2,
    ManagedAssetLifecycleRejectedV2,
    ManagedAssetLifecycleStateV2,
    _snapshot_state_v2,
)


def _require_exact_v2(value: object, expected_type: type[object], *, name: str) -> None:
    if type(value) is not expected_type:
        raise TypeError(f"{name} must be exact")


def _require_none_authority_v2(value: object, *, name: str) -> None:
    if type(value) is not str or value != "NONE":
        raise ValueError(f"{name} must remain NONE")


def _snapshot_effect_plan_v2(value: GlobalEconomicEffectPlanV2) -> GlobalEconomicEffectPlanV2:
    _require_exact_v2(value, GlobalEconomicEffectPlanV2, name="wire effect plan")
    return GlobalEconomicEffectPlanV2(
        value.rows,
        value.asset_conservation,
        value.fee_conservation,
        value.lane_writes,
        value.occurrence_consumptions,
        value.external_outbox_enqueue,
    )


def _snapshot_terminal_plan_v2(
    value: GlobalTerminalObligationPlanV2,
) -> GlobalTerminalObligationPlanV2:
    _require_exact_v2(value, GlobalTerminalObligationPlanV2, name="wire terminal plan")
    return GlobalTerminalObligationPlanV2(value.deltas)


def _snapshot_oracle_plan_v2(
    value: GlobalOracleOccurrencePlanV2,
) -> GlobalOracleOccurrencePlanV2:
    _require_exact_v2(value, GlobalOracleOccurrencePlanV2, name="wire Oracle plan")
    return GlobalOracleOccurrencePlanV2(value.deltas)


def _snapshot_occurrences_v2(
    values: object,
    *,
    name: str,
) -> tuple[EconomicCommandOccurrenceV2, ...]:
    raw = require_raw_tuple_ceiling_v2(
        values,
        name=name,
        ceiling=MAX_CONSUMED_OCCURRENCES_PER_REFINEMENT_V2,
    )
    if any(type(value) is not EconomicCommandOccurrenceV2 for value in raw):
        raise TypeError(f"{name} must contain exact occurrences")
    return tuple(_snapshot_occurrence_v2(cast(EconomicCommandOccurrenceV2, value)) for value in raw)


def _snapshot_outbox_v2(
    values: object,
    *,
    name: str,
) -> tuple[ExternalOutboxEnqueueV2, ...]:
    if type(values) is not tuple:
        raise TypeError(f"{name} must be a tuple")
    if any(type(value) is not ExternalOutboxEnqueueV2 for value in values):
        raise TypeError(f"{name} must contain exact external outbox rows")
    return tuple(replace(value) for value in values)


def _validate_leaf_acceptance_v2(
    *,
    post_state: AssetLaneStateV2 | AssetOriginRegistryStateV2 | ManagedAssetLifecycleStateV2,
    effects: GlobalEconomicEffectPlanV2,
    journal: LaneModuleTransitionJournalV2,
    name: str,
) -> None:
    if effects.is_empty:
        raise ValueError(f"{name} requires nonempty effects")
    if journal.lane_id is not LaneIdV2.ASSET_TRANSFER:
        raise ValueError(f"{name} journal has the wrong lane")
    if journal.module_release_id != post_state.module_release_id:
        raise ValueError(f"{name} journal has the wrong module release")
    if journal.post_lane_root != post_state.state_root:
        raise ValueError(f"{name} journal has the wrong post-state root")
    if journal.effect_plan_root != effects.effect_plan_root:
        raise ValueError(f"{name} journal has the wrong effect root")
    if effects.occurrence_consumptions != (journal.command_occurrence_id,):
        raise ValueError(f"{name} effects have the wrong occurrence")
    if effects.lane_writes != (
        LaneWriteV2(LaneIdV2.ASSET_TRANSFER, journal.pre_lane_root, journal.post_lane_root),
    ):
        raise ValueError(f"{name} effects have the wrong lane write")
    if (
        journal.private_port_root != ZERO_ROOT_V2
        or journal.terminal_obligations_root != ZERO_ROOT_V2
        or journal.oracle_occurrence_plan_root != ZERO_ROOT_V2
    ):
        raise ValueError(f"{name} has nonzero external roots")


def _validate_noop_v2(
    *,
    pre_state_root: str,
    post_state_root: str,
    effects: GlobalEconomicEffectPlanV2,
    name: str,
) -> None:
    _require_root_v2(pre_state_root, name=f"{name} pre-state root")
    _require_root_v2(post_state_root, name=f"{name} post-state root")
    if pre_state_root != post_state_root or not effects.is_empty:
        raise ValueError(f"{name} must be an exact no-op")


@dataclass(frozen=True, slots=True)
class GlobalEconomicStateEffectRefinementWireV2:
    pre_state_root: str
    post_state_root: str
    effect_plan_root: str
    terminal_plan_root: str
    oracle_plan_root: str
    state_delta_root: str
    production_authority: str
    refinement_root: str

    def __post_init__(self) -> None:
        for field_name in (
            "pre_state_root",
            "post_state_root",
            "effect_plan_root",
            "state_delta_root",
            "refinement_root",
        ):
            _require_root_v2(getattr(self, field_name), name=f"wire refinement {field_name}")
        _require_root_v2(
            self.terminal_plan_root,
            name="wire refinement terminal plan root",
            allow_zero=True,
        )
        _require_root_v2(
            self.oracle_plan_root,
            name="wire refinement Oracle plan root",
            allow_zero=True,
        )
        _require_none_authority_v2(
            self.production_authority,
            name="wire refinement production authority",
        )
        expected = hash_global_v2(
            "global-economic-state-effect-refinement-v2",
            {
                "schema": GLOBAL_ECONOMIC_STATE_EFFECT_REFINEMENT_SCHEMA_V2,
                "pre_state_root": self.pre_state_root,
                "post_state_root": self.post_state_root,
                "effect_plan_root": self.effect_plan_root,
                "terminal_plan_root": self.terminal_plan_root,
                "oracle_plan_root": self.oracle_plan_root,
                "state_delta_root": self.state_delta_root,
            },
        )
        if self.refinement_root != expected:
            raise ValueError("wire refinement root does not bind its fields")

    def to_canonical(self) -> dict[str, object]:
        return {
            "pre_state_root": self.pre_state_root,
            "post_state_root": self.post_state_root,
            "effect_plan_root": self.effect_plan_root,
            "terminal_plan_root": self.terminal_plan_root,
            "oracle_plan_root": self.oracle_plan_root,
            "state_delta_root": self.state_delta_root,
            "production_authority": self.production_authority,
            "refinement_root": self.refinement_root,
        }


@dataclass(frozen=True, slots=True)
class GlobalEconomicRefinementAcceptedWireV2:
    witness: GlobalEconomicStateEffectRefinementWireV2
    production_authority: str

    def __post_init__(self) -> None:
        _require_exact_v2(
            self.witness,
            GlobalEconomicStateEffectRefinementWireV2,
            name="wire global refinement accepted witness",
        )
        _require_none_authority_v2(
            self.production_authority,
            name="wire global refinement accepted authority",
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "witness": self.witness,
            "production_authority": self.production_authority,
        }


@dataclass(frozen=True, slots=True)
class GlobalEconomicRefinementRejectedWireV2:
    reject_code: GlobalEconomicRefinementRejectCodeV2
    pre_state_root: str
    post_state_root: str
    effect_plan: GlobalEconomicEffectPlanV2
    terminal_plan: GlobalTerminalObligationPlanV2
    oracle_plan: GlobalOracleOccurrencePlanV2
    consumed_occurrences: tuple[EconomicCommandOccurrenceV2, ...]
    outbox: tuple[ExternalOutboxEnqueueV2, ...]
    production_authority: str

    def __post_init__(self) -> None:
        occurrences = _snapshot_occurrences_v2(
            self.consumed_occurrences,
            name="wire global refinement rejected occurrences",
        )
        _require_exact_v2(
            self.reject_code,
            GlobalEconomicRefinementRejectCodeV2,
            name="wire global refinement rejected code",
        )
        effects = _snapshot_effect_plan_v2(self.effect_plan)
        terminal = _snapshot_terminal_plan_v2(self.terminal_plan)
        oracle = _snapshot_oracle_plan_v2(self.oracle_plan)
        outbox = _snapshot_outbox_v2(self.outbox, name="wire global refinement rejected outbox")
        _validate_noop_v2(
            pre_state_root=self.pre_state_root,
            post_state_root=self.post_state_root,
            effects=effects,
            name="wire global refinement rejection",
        )
        if terminal.deltas or oracle.deltas or occurrences or outbox:
            raise ValueError("wire global refinement rejection carries a non-noop field")
        _require_none_authority_v2(
            self.production_authority,
            name="wire global refinement rejected authority",
        )
        object.__setattr__(self, "effect_plan", effects)
        object.__setattr__(self, "terminal_plan", terminal)
        object.__setattr__(self, "oracle_plan", oracle)
        object.__setattr__(self, "consumed_occurrences", occurrences)
        object.__setattr__(self, "outbox", outbox)

    def to_canonical(self) -> dict[str, object]:
        return {
            "reject_code": self.reject_code,
            "pre_state_root": self.pre_state_root,
            "post_state_root": self.post_state_root,
            "effect_plan": self.effect_plan,
            "terminal_plan": self.terminal_plan,
            "oracle_plan": self.oracle_plan,
            "consumed_occurrences": self.consumed_occurrences,
            "outbox": self.outbox,
            "production_authority": self.production_authority,
        }


@dataclass(frozen=True, slots=True)
class ManagedAssetLifecycleAcceptedWireV2:
    post_state: ManagedAssetLifecycleStateV2
    effects: GlobalEconomicEffectPlanV2
    module_journal: LaneModuleTransitionJournalV2
    receipt_root: str
    production_authority: str

    def __post_init__(self) -> None:
        state = _snapshot_state_v2(self.post_state)
        effects = _snapshot_effect_plan_v2(self.effects)
        journal = _snapshot_module_journal_v2(self.module_journal)
        _validate_leaf_acceptance_v2(
            post_state=state,
            effects=effects,
            journal=journal,
            name="wire managed asset acceptance",
        )
        _require_root_v2(self.receipt_root, name="wire managed asset receipt root")
        if self.receipt_root != journal.receipt_root:
            raise ValueError("wire managed asset receipt root differs from journal")
        _require_none_authority_v2(
            self.production_authority,
            name="wire managed asset production authority",
        )
        object.__setattr__(self, "post_state", state)
        object.__setattr__(self, "effects", effects)
        object.__setattr__(self, "module_journal", journal)

    def to_canonical(self) -> dict[str, object]:
        return {
            "post_state": self.post_state,
            "effects": self.effects,
            "module_journal": self.module_journal,
            "receipt_root": self.receipt_root,
            "production_authority": self.production_authority,
        }


@dataclass(frozen=True, slots=True)
class ManagedAssetLifecycleRejectedWireV2:
    code: ManagedAssetLifecycleRejectCodeV2
    pre_state_root: str
    post_state_root: str
    effects: GlobalEconomicEffectPlanV2
    terminal_obligations_root: str
    oracle_occurrence_plan_root: str
    production_authority: str

    def __post_init__(self) -> None:
        _require_exact_v2(
            self.code, ManagedAssetLifecycleRejectCodeV2, name="wire managed reject code"
        )
        effects = _snapshot_effect_plan_v2(self.effects)
        _validate_noop_v2(
            pre_state_root=self.pre_state_root,
            post_state_root=self.post_state_root,
            effects=effects,
            name="wire managed asset rejection",
        )
        if (
            self.terminal_obligations_root != ZERO_ROOT_V2
            or self.oracle_occurrence_plan_root != ZERO_ROOT_V2
        ):
            raise ValueError("wire managed asset rejection has nonzero lifecycle roots")
        _require_none_authority_v2(
            self.production_authority,
            name="wire managed asset rejection authority",
        )
        object.__setattr__(self, "effects", effects)

    def to_canonical(self) -> dict[str, object]:
        return {
            "code": self.code,
            "pre_state_root": self.pre_state_root,
            "post_state_root": self.post_state_root,
            "effects": self.effects,
            "terminal_obligations_root": self.terminal_obligations_root,
            "oracle_occurrence_plan_root": self.oracle_occurrence_plan_root,
            "production_authority": self.production_authority,
        }


@dataclass(frozen=True, slots=True)
class AssetOriginRegistrationAcceptedWireV2:
    post_state: AssetOriginRegistryStateV2
    effects: GlobalEconomicEffectPlanV2
    module_journal: LaneModuleTransitionJournalV2
    production_authority: str

    def __post_init__(self) -> None:
        state = _snapshot_registry_state_v2(self.post_state)
        effects = _snapshot_effect_plan_v2(self.effects)
        journal = _snapshot_module_journal_v2(self.module_journal)
        _validate_leaf_acceptance_v2(
            post_state=state,
            effects=effects,
            journal=journal,
            name="wire asset origin acceptance",
        )
        if effects.rows or effects.asset_conservation or effects.fee_conservation:
            raise ValueError("wire asset origin acceptance creates economic value")
        if effects.external_outbox_enqueue:
            raise ValueError("wire asset origin acceptance creates an external outbox")
        _require_none_authority_v2(
            self.production_authority,
            name="wire asset origin production authority",
        )
        object.__setattr__(self, "post_state", state)
        object.__setattr__(self, "effects", effects)
        object.__setattr__(self, "module_journal", journal)

    def to_canonical(self) -> dict[str, object]:
        return {
            "post_state": self.post_state,
            "effects": self.effects,
            "module_journal": self.module_journal,
            "production_authority": self.production_authority,
        }


@dataclass(frozen=True, slots=True)
class AssetOriginRegistrationRejectedWireV2:
    code: AssetOriginRegistrationRejectCodeV2
    pre_state_root: str
    post_state_root: str
    effects: GlobalEconomicEffectPlanV2

    def __post_init__(self) -> None:
        _require_exact_v2(
            self.code, AssetOriginRegistrationRejectCodeV2, name="wire origin reject code"
        )
        effects = _snapshot_effect_plan_v2(self.effects)
        _validate_noop_v2(
            pre_state_root=self.pre_state_root,
            post_state_root=self.post_state_root,
            effects=effects,
            name="wire asset origin rejection",
        )
        object.__setattr__(self, "effects", effects)

    def to_canonical(self) -> dict[str, object]:
        return {
            "code": self.code,
            "pre_state_root": self.pre_state_root,
            "post_state_root": self.post_state_root,
            "effects": self.effects,
        }


@dataclass(frozen=True, slots=True)
class AssetLaneContextWireV2:
    writer_epoch: int
    module_release_id: str
    global_pre_state_root: str
    occurrence: EconomicCommandOccurrenceV2 | None

    def __post_init__(self) -> None:
        context = AssetLaneContextV2(
            self.writer_epoch,
            self.module_release_id,
            self.global_pre_state_root,
            self.occurrence,
        )
        object.__setattr__(self, "writer_epoch", context.writer_epoch)
        object.__setattr__(self, "module_release_id", context.module_release_id)
        object.__setattr__(self, "global_pre_state_root", context.global_pre_state_root)
        object.__setattr__(self, "occurrence", context.occurrence)

    def to_domain_v2(self) -> AssetLaneContextV2:
        """Return the safe context input represented by this wire record."""

        return AssetLaneContextV2(
            self.writer_epoch,
            self.module_release_id,
            self.global_pre_state_root,
            self.occurrence,
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "writer_epoch": self.writer_epoch,
            "module_release_id": self.module_release_id,
            "global_pre_state_root": self.global_pre_state_root,
            "occurrence": self.occurrence,
        }


@dataclass(frozen=True, slots=True)
class AssetLaneAcceptedWireV2:
    route: AssetLaneRouteV2
    source_leaf_journal_root: str
    post_state: AssetLaneStateV2
    effects: GlobalEconomicEffectPlanV2
    module_journal: LaneModuleTransitionJournalV2
    receipt_root: str
    production_authority: str
    profile_authentication: str

    def __post_init__(self) -> None:
        if type(self.route) is not AssetLaneRouteV2 or self.route is AssetLaneRouteV2.COORDINATOR:
            raise TypeError("wire asset lane accepted route must name a leaf")
        _require_root_v2(
            self.source_leaf_journal_root,
            name="wire asset lane source leaf journal root",
        )
        state = _snapshot_asset_lane_state_v2(self.post_state)
        effects = _snapshot_effect_plan_v2(self.effects)
        journal = _snapshot_module_journal_v2(self.module_journal)
        _validate_leaf_acceptance_v2(
            post_state=state,
            effects=effects,
            journal=journal,
            name="wire asset lane acceptance",
        )
        if effects.external_outbox_enqueue:
            raise ValueError("wire asset lane acceptance has an external outbox")
        _require_root_v2(self.receipt_root, name="wire asset lane receipt root")
        if self.receipt_root != journal.receipt_root:
            raise ValueError("wire asset lane receipt root differs from journal")
        if not _policy_origin_bindings_hold_v2(state):
            raise ValueError("wire asset lane policy-origin binding differs")
        _require_none_authority_v2(
            self.production_authority,
            name="wire asset lane production authority",
        )
        if self.profile_authentication != ASSET_LANE_PROFILE_AUTHENTICATION_V2:
            raise ValueError("wire asset lane profile authentication must remain SHADOW")
        object.__setattr__(self, "post_state", state)
        object.__setattr__(self, "effects", effects)
        object.__setattr__(self, "module_journal", journal)

    def to_canonical(self) -> dict[str, object]:
        return {
            "route": self.route,
            "source_leaf_journal_root": self.source_leaf_journal_root,
            "post_state": self.post_state,
            "effects": self.effects,
            "module_journal": self.module_journal,
            "receipt_root": self.receipt_root,
            "production_authority": self.production_authority,
            "profile_authentication": self.profile_authentication,
        }


@dataclass(frozen=True, slots=True)
class AssetLaneRejectedWireV2:
    route: AssetLaneRouteV2
    code: AssetLaneRejectCodeV2
    pre_state_root: str
    post_state_root: str
    effects: GlobalEconomicEffectPlanV2
    production_authority: str
    profile_authentication: str

    def __post_init__(self) -> None:
        code_type_by_route = {
            AssetLaneRouteV2.COORDINATOR: AssetLaneCoordinatorRejectCodeV2,
            AssetLaneRouteV2.TRANSFER: AssetTransferRejectCodeV2,
            AssetLaneRouteV2.MANAGED_LIFECYCLE: ManagedAssetLifecycleRejectCodeV2,
        }
        if type(self.route) is not AssetLaneRouteV2 or type(
            self.code
        ) is not code_type_by_route.get(self.route):
            raise TypeError("wire asset lane rejection is not closed")
        effects = _snapshot_effect_plan_v2(self.effects)
        _validate_noop_v2(
            pre_state_root=self.pre_state_root,
            post_state_root=self.post_state_root,
            effects=effects,
            name="wire asset lane rejection",
        )
        _require_none_authority_v2(
            self.production_authority,
            name="wire asset lane rejection authority",
        )
        if self.profile_authentication != ASSET_LANE_PROFILE_AUTHENTICATION_V2:
            raise ValueError("wire asset lane profile authentication must remain SHADOW")
        object.__setattr__(self, "effects", effects)

    def to_canonical(self) -> dict[str, object]:
        return {
            "route": self.route,
            "code": self.code,
            "pre_state_root": self.pre_state_root,
            "post_state_root": self.post_state_root,
            "effects": self.effects,
            "production_authority": self.production_authority,
            "profile_authentication": self.profile_authentication,
        }


@dataclass(frozen=True, slots=True)
class GlobalEconomicStateEffectRefinementCandidateWireV2:
    pre_state: GlobalEconomicStateV2
    post_state: GlobalEconomicStateV2
    effect_plan: GlobalEconomicEffectPlanV2
    consumed_occurrences: tuple[EconomicCommandOccurrenceV2, ...]
    terminal_plan: GlobalTerminalObligationPlanV2
    oracle_plan: GlobalOracleOccurrencePlanV2

    def __post_init__(self) -> None:
        occurrences = _snapshot_occurrences_v2(
            self.consumed_occurrences,
            name="wire global refinement candidate occurrences",
        )
        pre_state = snapshot_global_economic_state_v2(self.pre_state)
        post_state = snapshot_global_economic_state_v2(self.post_state)
        effects = _snapshot_effect_plan_v2(self.effect_plan)
        terminal = _snapshot_terminal_plan_v2(self.terminal_plan)
        oracle = _snapshot_oracle_plan_v2(self.oracle_plan)
        object.__setattr__(self, "pre_state", pre_state)
        object.__setattr__(self, "post_state", post_state)
        object.__setattr__(self, "effect_plan", effects)
        # Preserve supplied occurrence order so the core can expose its stable
        # OCCURRENCES_NOT_ORDERED_UNIQUE rejection when applicable.
        object.__setattr__(self, "consumed_occurrences", occurrences)
        object.__setattr__(self, "terminal_plan", terminal)
        object.__setattr__(self, "oracle_plan", oracle)

    def to_domain_v2(self) -> GlobalEconomicStateEffectRefinementCandidateV2:
        """Return the safe candidate input represented by this wire record."""

        return GlobalEconomicStateEffectRefinementCandidateV2(
            self.pre_state,
            self.post_state,
            self.effect_plan,
            self.consumed_occurrences,
            self.terminal_plan,
            self.oracle_plan,
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "pre_state": self.pre_state,
            "post_state": self.post_state,
            "effect_plan": self.effect_plan,
            "consumed_occurrences": self.consumed_occurrences,
            "terminal_plan": self.terminal_plan,
            "oracle_plan": self.oracle_plan,
        }


WireRecordV2: TypeAlias = (
    GlobalEconomicRefinementAcceptedWireV2
    | GlobalEconomicRefinementRejectedWireV2
    | ManagedAssetLifecycleAcceptedWireV2
    | ManagedAssetLifecycleRejectedWireV2
    | AssetOriginRegistrationAcceptedWireV2
    | AssetOriginRegistrationRejectedWireV2
    | AssetLaneContextWireV2
    | AssetLaneAcceptedWireV2
    | AssetLaneRejectedWireV2
    | GlobalEconomicStateEffectRefinementCandidateWireV2
    | GlobalEconomicStateEffectRefinementWireV2
)

WIRE_RECORD_TYPES_V2: Final[tuple[type[object], ...]] = (
    GlobalEconomicRefinementAcceptedWireV2,
    GlobalEconomicRefinementRejectedWireV2,
    ManagedAssetLifecycleAcceptedWireV2,
    ManagedAssetLifecycleRejectedWireV2,
    AssetOriginRegistrationAcceptedWireV2,
    AssetOriginRegistrationRejectedWireV2,
    AssetLaneContextWireV2,
    AssetLaneAcceptedWireV2,
    AssetLaneRejectedWireV2,
    GlobalEconomicStateEffectRefinementCandidateWireV2,
    GlobalEconomicStateEffectRefinementWireV2,
)


def wire_record_from_domain_v2(value: object) -> WireRecordV2:
    """Project one exact V2 value into a strict wire-only record.

    This function never reconstructs an accepted domain witness from bytes.
    The reverse conversion is intentionally present only on context/candidate
    records, whose target types are ordinary deterministic inputs.
    """

    if type(value) in WIRE_RECORD_TYPES_V2:
        return cast(WireRecordV2, value)
    if type(value) is GlobalEconomicRefinementAcceptedV2:
        global_accepted = value
        witness = global_accepted.witness
        return GlobalEconomicRefinementAcceptedWireV2(
            GlobalEconomicStateEffectRefinementWireV2(
                witness.pre_state_root,
                witness.post_state_root,
                witness.effect_plan_root,
                witness.terminal_plan_root,
                witness.oracle_plan_root,
                witness.state_delta_root,
                witness.production_authority,
                witness.refinement_root,
            ),
            global_accepted.production_authority,
        )
    if type(value) is GlobalEconomicRefinementRejectedV2:
        global_rejected = value
        return GlobalEconomicRefinementRejectedWireV2(
            global_rejected.reject_code,
            global_rejected.pre_state_root,
            global_rejected.post_state_root,
            global_rejected.effect_plan,
            global_rejected.terminal_plan,
            global_rejected.oracle_plan,
            global_rejected.consumed_occurrences,
            global_rejected.outbox,
            global_rejected.production_authority,
        )
    if type(value) is ManagedAssetLifecycleAcceptedV2:
        managed_accepted = cast(ManagedAssetLifecycleAcceptedV2, value)
        return ManagedAssetLifecycleAcceptedWireV2(
            managed_accepted.post_state,
            managed_accepted.effects,
            managed_accepted.module_journal,
            managed_accepted.receipt_root,
            managed_accepted.production_authority,
        )
    if type(value) is ManagedAssetLifecycleRejectedV2:
        managed_rejected = cast(ManagedAssetLifecycleRejectedV2, value)
        return ManagedAssetLifecycleRejectedWireV2(
            managed_rejected.code,
            managed_rejected.pre_state_root,
            managed_rejected.post_state_root,
            managed_rejected.effects,
            managed_rejected.terminal_obligations_root,
            managed_rejected.oracle_occurrence_plan_root,
            managed_rejected.production_authority,
        )
    if type(value) is AssetOriginRegistrationAcceptedV2:
        origin_accepted = value
        return AssetOriginRegistrationAcceptedWireV2(
            origin_accepted.post_state,
            origin_accepted.effects,
            origin_accepted.module_journal,
            origin_accepted.production_authority,
        )
    if type(value) is AssetOriginRegistrationRejectedV2:
        origin_rejected = value
        return AssetOriginRegistrationRejectedWireV2(
            origin_rejected.code,
            origin_rejected.pre_state_root,
            origin_rejected.post_state_root,
            origin_rejected.effects,
        )
    if type(value) is AssetLaneContextV2:
        context = value
        return AssetLaneContextWireV2(
            context.writer_epoch,
            context.module_release_id,
            context.global_pre_state_root,
            context.occurrence,
        )
    if type(value) is AssetLaneAcceptedV2:
        accepted = cast(AssetLaneAcceptedV2, value)
        return AssetLaneAcceptedWireV2(
            accepted.route,
            accepted.source_leaf_journal_root,
            accepted.post_state,
            accepted.effects,
            accepted.module_journal,
            accepted.receipt_root,
            accepted.production_authority,
            accepted.profile_authentication,
        )
    if type(value) is AssetLaneRejectedV2:
        rejected = cast(AssetLaneRejectedV2, value)
        return AssetLaneRejectedWireV2(
            rejected.route,
            rejected.code,
            rejected.pre_state_root,
            rejected.post_state_root,
            rejected.effects,
            rejected.production_authority,
            rejected.profile_authentication,
        )
    if type(value) is GlobalEconomicStateEffectRefinementCandidateV2:
        candidate = value
        return GlobalEconomicStateEffectRefinementCandidateWireV2(
            candidate.pre_state,
            candidate.post_state,
            candidate.effect_plan,
            candidate.consumed_occurrences,
            candidate.terminal_plan,
            candidate.oracle_plan,
        )
    if type(value) is GlobalEconomicStateEffectRefinementV2:
        refinement = value
        return GlobalEconomicStateEffectRefinementWireV2(
            refinement.pre_state_root,
            refinement.post_state_root,
            refinement.effect_plan_root,
            refinement.terminal_plan_root,
            refinement.oracle_plan_root,
            refinement.state_delta_root,
            refinement.production_authority,
            refinement.refinement_root,
        )
    raise TypeError("value has no strict V2 wire record projection")


__all__ = [
    "GlobalEconomicRefinementAcceptedWireV2",
    "GlobalEconomicRefinementRejectedWireV2",
    "ManagedAssetLifecycleAcceptedWireV2",
    "ManagedAssetLifecycleRejectedWireV2",
    "AssetOriginRegistrationAcceptedWireV2",
    "AssetOriginRegistrationRejectedWireV2",
    "AssetLaneContextWireV2",
    "AssetLaneAcceptedWireV2",
    "AssetLaneRejectedWireV2",
    "GlobalEconomicStateEffectRefinementCandidateWireV2",
    "GlobalEconomicStateEffectRefinementWireV2",
    "WireRecordV2",
    "WIRE_RECORD_TYPES_V2",
    "wire_record_from_domain_v2",
]
