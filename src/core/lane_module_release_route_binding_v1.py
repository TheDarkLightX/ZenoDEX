"""Structural active-profile binding for accepted lane-module outputs.

This core closes profile, route, release, occurrence, command, and domain
bindings before lane composition. It does not verify a cryptographic receipt
and grants no settlement or publication authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final, Protocol

from .asset_transfer_lane_module_v1 import (
    AssetTransferLaneModuleAcceptedV1,
    AssetTransferLaneModuleInputV1,
    _recompute_asset_transfer_lane_module_accepted_v1,
)
from .global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from .global_economic_proof_v1 import (
    EconomicCommandOccurrenceV1,
    LaneModuleTransitionJournalV1,
)
from .global_economic_refinement_snapshot_v1 import _snapshot_occurrence_v1
from .global_oracle_price_occurrence_v1 import VerifiedGlobalOraclePriceV1
from .global_settlement_types_v1 import (
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    LaneIdV1,
    ProfileStatusV1,
    hash_global_v1,
)
from .managed_asset_lifecycle_lane_module_v1 import (
    ManagedAssetLifecycleLaneModuleAcceptedV1,
    ManagedAssetLifecycleLaneModuleInputV1,
    _recompute_managed_asset_lifecycle_lane_module_accepted_v1,
    _snapshot_managed_asset_lifecycle_lane_module_accepted_v1,
    _snapshot_managed_asset_lifecycle_lane_module_input_v1,
)
from .managed_asset_policy_registry_v1 import (
    ManagedAssetPolicyRegistryV1,
    require_governed_managed_asset_policy_registry_v1,
    require_managed_asset_policy_membership_v1,
    require_managed_asset_route_policy_root_v1,
    snapshot_exact_economic_policy_registry_v1,
    snapshot_managed_asset_policy_registry_v1,
)
from .perps_margin_lane_module_v1 import (
    PerpsMarginLaneModuleInputV1,
    _recompute_perps_margin_accepted_v1,
)
from .perps_margin_types_v1 import (
    PERPS_MARGIN_MODULE_SCHEMA_V1,
    PerpsMarginAcceptedV1,
)
from .perps_market_policy_v1 import (
    PerpsMarketPolicyV1,
    require_governed_perps_market_policy_v1,
)

RELEASE_ROUTE_BOUND_LANE_TRANSITION_SCHEMA_V1: Final = (
    "zenodex/release-route-bound-lane-transition/v1"
)
_RELEASE_ROUTE_BOUND_TOKEN = object()


class ReleaseRouteBoundLaneTransitionV1:
    """Opaque structural witness produced only by the release-route binder."""

    _profile_id: str
    _route_release_id: str
    _lane_id: LaneIdV1
    _module_release_id: str
    _command_occurrence_id: str
    _module_journal_root: str
    _statement_root: str
    _producer_module_schema: str
    _route_lane_index: int
    _port_schema_root: str

    __slots__ = (
        "_profile_id",
        "_route_release_id",
        "_lane_id",
        "_module_release_id",
        "_command_occurrence_id",
        "_module_journal_root",
        "_statement_root",
        "_producer_module_schema",
        "_route_lane_index",
        "_port_schema_root",
    )

    def __init__(
        self,
        token: object,
        profile_id: str,
        route_release_id: str,
        lane_id: LaneIdV1,
        module_release_id: str,
        command_occurrence_id: str,
        module_journal_root: str,
        statement_root: str,
        producer_module_schema: str,
        route_lane_index: int,
        port_schema_root: str,
    ) -> None:
        if token is not _RELEASE_ROUTE_BOUND_TOKEN:
            raise TypeError("ReleaseRouteBoundLaneTransitionV1 is binder-constructed")
        object.__setattr__(self, "_profile_id", profile_id)
        object.__setattr__(self, "_route_release_id", route_release_id)
        object.__setattr__(self, "_lane_id", lane_id)
        object.__setattr__(self, "_module_release_id", module_release_id)
        object.__setattr__(self, "_command_occurrence_id", command_occurrence_id)
        object.__setattr__(self, "_module_journal_root", module_journal_root)
        object.__setattr__(self, "_statement_root", statement_root)
        object.__setattr__(self, "_producer_module_schema", producer_module_schema)
        object.__setattr__(self, "_route_lane_index", route_lane_index)
        object.__setattr__(self, "_port_schema_root", port_schema_root)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("ReleaseRouteBoundLaneTransitionV1 is immutable")

    @property
    def profile_id(self) -> str:
        return self._profile_id

    @property
    def route_release_id(self) -> str:
        return self._route_release_id

    @property
    def lane_id(self) -> LaneIdV1:
        return self._lane_id

    @property
    def module_release_id(self) -> str:
        return self._module_release_id

    @property
    def command_occurrence_id(self) -> str:
        return self._command_occurrence_id

    @property
    def module_journal_root(self) -> str:
        return self._module_journal_root

    @property
    def statement_root(self) -> str:
        return self._statement_root

    @property
    def producer_module_schema(self) -> str:
        return self._producer_module_schema

    @property
    def route_lane_index(self) -> int:
        return self._route_lane_index

    @property
    def port_schema_root(self) -> str:
        return self._port_schema_root

    @property
    def binding_root(self) -> str:
        return hash_global_v1(
            "release-route-bound-lane-transition-v1",
            {
                "schema": RELEASE_ROUTE_BOUND_LANE_TRANSITION_SCHEMA_V1,
                "profile_id": self.profile_id,
                "route_release_id": self.route_release_id,
                "lane_id": self.lane_id,
                "module_release_id": self.module_release_id,
                "command_occurrence_id": self.command_occurrence_id,
                "module_journal_root": self.module_journal_root,
                "statement_root": self.statement_root,
                "producer_module_schema": self.producer_module_schema,
                "route_lane_index": self.route_lane_index,
                "port_schema_root": self.port_schema_root,
            },
        )


@dataclass(frozen=True, slots=True)
class _BindingCandidateV1:
    actual_command_kind: str
    command_body_hash: str
    statement_root: str
    producer_module_schema: str
    context: _ModuleContextV1
    module_journal: LaneModuleTransitionJournalV1


class _ModuleContextV1(Protocol):
    chain_id: str
    deployment_root: str
    profile_root: str
    writer_epoch: int
    module_release_id: str
    command_occurrence_id: str
    subject_id: str
    grant_root: str


def _require_exact_context_binding(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    candidate: _BindingCandidateV1,
) -> None:
    context = candidate.context
    bindings = (
        (context.subject_id, occurrence.subject_id, "subject"),
        (context.grant_root, occurrence.grant_root, "grant root"),
        (context.chain_id, occurrence.chain_id, "chain id"),
        (context.deployment_root, occurrence.deployment_root, "deployment root"),
        (context.profile_root, profile.profile_id, "profile root"),
        (context.command_occurrence_id, occurrence.occurrence_id, "command occurrence"),
    )
    for actual, expected, label in bindings:
        if actual != expected:
            raise ValueError(f"lane module release-route {label} mismatch")
    if context.writer_epoch != profile.authority_epoch:
        raise ValueError("lane module release-route writer epoch mismatch")


def _require_exact_journal_binding(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    candidate: _BindingCandidateV1,
) -> None:
    journal = candidate.module_journal
    bindings = (
        (journal.chain_id, occurrence.chain_id, "journal chain id"),
        (journal.deployment_root, occurrence.deployment_root, "journal deployment root"),
        (journal.profile_root, profile.profile_id, "journal profile root"),
        (journal.command_occurrence_id, occurrence.occurrence_id, "journal occurrence"),
    )
    for actual, expected, label in bindings:
        if actual != expected:
            raise ValueError(f"lane module release-route {label} mismatch")
    if journal.writer_epoch != profile.authority_epoch:
        raise ValueError("lane module release-route journal writer epoch mismatch")


def _bind_candidate_v1(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    candidate: _BindingCandidateV1,
) -> ReleaseRouteBoundLaneTransitionV1:
    if profile.status is not ProfileStatusV1.ACTIVE:
        raise ValueError("economic profile is not ACTIVE")
    route = profile.route_registry.route_for_command(
        occurrence.command_kind,
        claimed_route_release_id=occurrence.route_release_id,
    )
    if candidate.actual_command_kind != occurrence.command_kind:
        raise ValueError("lane module release-route command kind mismatch")
    if candidate.command_body_hash != occurrence.command_body_hash:
        raise ValueError("lane module release-route command body hash mismatch")
    _require_exact_context_binding(profile, occurrence, candidate)
    _require_exact_journal_binding(profile, occurrence, candidate)

    journal = candidate.module_journal
    try:
        route_lane_index = route.ordered_lanes.index(journal.lane_id)
    except ValueError as exc:
        raise ValueError("lane module release-route lane mismatch") from exc
    release = profile.lane_registry.release_for(journal.lane_id)
    if (
        journal.module_release_id != release.release_id
        or route.module_release_ids[route_lane_index] != release.release_id
        or candidate.context.module_release_id != release.release_id
    ):
        raise ValueError("lane module release-route module release mismatch")
    if candidate.actual_command_kind not in release.command_variants:
        raise ValueError("lane module command is absent from the governed release")

    return ReleaseRouteBoundLaneTransitionV1(
        _RELEASE_ROUTE_BOUND_TOKEN,
        profile.profile_id,
        route.route_release_id,
        journal.lane_id,
        release.release_id,
        occurrence.occurrence_id,
        journal.journal_root,
        candidate.statement_root,
        candidate.producer_module_schema,
        route_lane_index,
        route.port_schema_roots[route_lane_index],
    )


def bind_asset_transfer_lane_output_to_release_route_v1(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    module_input: AssetTransferLaneModuleInputV1,
    accepted: AssetTransferLaneModuleAcceptedV1,
) -> ReleaseRouteBoundLaneTransitionV1:
    """Bind one accepted transfer output to its governed active route."""

    if type(profile) is not EconomicProfileSnapshotV1:
        raise TypeError("economic profile must have the exact typed value")
    if type(occurrence) is not EconomicCommandOccurrenceV1:
        raise TypeError("economic command occurrence must have the exact typed value")
    if type(module_input) is not AssetTransferLaneModuleInputV1:
        raise TypeError("asset transfer lane input must have the exact typed value")
    if type(accepted) is not AssetTransferLaneModuleAcceptedV1:
        raise TypeError("asset transfer accepted output must have the exact typed value")
    owned_input, expected = _recompute_asset_transfer_lane_module_accepted_v1(
        module_input,
        accepted,
    )
    return _bind_candidate_v1(
        profile,
        occurrence,
        _BindingCandidateV1(
            owned_input.command.command_kind,
            owned_input.command.command_body_hash,
            expected.statement_root,
            expected.private_port.producer_module_schema,
            owned_input.context,
            expected.module_journal,
        ),
    )


@dataclass(frozen=True, slots=True)
class ManagedAssetLifecycleReleaseRouteBindingCandidateV1:
    """Exact typed inputs for one governed ordinary-token issue or burn binding."""

    profile: EconomicProfileSnapshotV1
    policy_registry: EconomicPolicyRegistryV1
    asset_policy_registry: ManagedAssetPolicyRegistryV1
    occurrence: EconomicCommandOccurrenceV1
    module_input: ManagedAssetLifecycleLaneModuleInputV1
    accepted: ManagedAssetLifecycleLaneModuleAcceptedV1

    def __post_init__(self) -> None:
        expected_types = (
            (self.profile, EconomicProfileSnapshotV1),
            (self.policy_registry, EconomicPolicyRegistryV1),
            (self.asset_policy_registry, ManagedAssetPolicyRegistryV1),
            (self.occurrence, EconomicCommandOccurrenceV1),
            (self.module_input, ManagedAssetLifecycleLaneModuleInputV1),
            (self.accepted, ManagedAssetLifecycleLaneModuleAcceptedV1),
        )
        if any(type(value) is not expected for value, expected in expected_types):
            raise TypeError("managed asset lifecycle route binding requires exact typed inputs")


def _snapshot_exact_occurrence_v1(
    occurrence: EconomicCommandOccurrenceV1,
) -> EconomicCommandOccurrenceV1:
    if type(occurrence) is not EconomicCommandOccurrenceV1:
        raise TypeError("economic command occurrence must have the exact typed value")
    return _snapshot_occurrence_v1(occurrence)


def _snapshot_managed_asset_route_binding_candidate_v1(
    candidate: ManagedAssetLifecycleReleaseRouteBindingCandidateV1,
) -> ManagedAssetLifecycleReleaseRouteBindingCandidateV1:
    """Own every candidate value exactly once, before any lookup or binding.

    Governed lookup, membership, the route policy-root check, and the route
    witness all read these owned values, so a retained alias mutated between
    steps cannot split the transaction into inconsistent reads.
    """

    if type(candidate) is not ManagedAssetLifecycleReleaseRouteBindingCandidateV1:
        raise TypeError("managed asset lifecycle route candidate must have the exact type")
    return ManagedAssetLifecycleReleaseRouteBindingCandidateV1(
        profile=snapshot_economic_profile_v1(candidate.profile),
        policy_registry=snapshot_exact_economic_policy_registry_v1(candidate.policy_registry),
        asset_policy_registry=snapshot_managed_asset_policy_registry_v1(
            candidate.asset_policy_registry
        ),
        occurrence=_snapshot_exact_occurrence_v1(candidate.occurrence),
        module_input=_snapshot_managed_asset_lifecycle_lane_module_input_v1(
            candidate.module_input
        ),
        accepted=_snapshot_managed_asset_lifecycle_lane_module_accepted_v1(candidate.accepted),
    )


def _require_managed_asset_policy_binding_v1(
    owned: ManagedAssetLifecycleReleaseRouteBindingCandidateV1,
    owned_input: ManagedAssetLifecycleLaneModuleInputV1,
) -> None:
    governed_registry = require_governed_managed_asset_policy_registry_v1(
        profile=owned.profile,
        policy_registry=owned.policy_registry,
        occurrence=owned.occurrence,
        asset_policy_registry=owned.asset_policy_registry,
    )
    require_managed_asset_policy_membership_v1(
        asset_policy_registry=governed_registry,
        module_input=owned_input,
    )
    require_managed_asset_route_policy_root_v1(
        profile=owned.profile,
        occurrence=owned.occurrence,
        asset_policy_registry=governed_registry,
    )


def bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
    candidate: ManagedAssetLifecycleReleaseRouteBindingCandidateV1,
) -> ReleaseRouteBoundLaneTransitionV1:
    """Bind one accepted ordinary-token issue or burn to its governed route.

    One owned snapshot of the profile, occurrence, both policy registries,
    input, and accepted output is taken first and used throughout. The command
    asset and every carried state policy must be exact members of the typed
    managed-asset policy registry that the active profile governs for the
    command kind, and the selected route's issue/burn policy root must be that
    registry's root, before the route witness is constructed.
    """

    owned = _snapshot_managed_asset_route_binding_candidate_v1(candidate)
    owned_input, expected = _recompute_managed_asset_lifecycle_lane_module_accepted_v1(
        owned.module_input,
        owned.accepted,
    )
    _require_managed_asset_policy_binding_v1(owned, owned_input)
    return _bind_candidate_v1(
        owned.profile,
        owned.occurrence,
        _BindingCandidateV1(
            owned_input.command.command_kind,
            owned_input.command.command_body_hash,
            expected.statement_root,
            expected.private_port.producer_module_schema,
            owned_input.context,
            expected.module_journal,
        ),
    )


@dataclass(frozen=True, slots=True)
class PerpsMarginReleaseRouteBindingCandidateV1:
    profile: EconomicProfileSnapshotV1
    policy_registry: EconomicPolicyRegistryV1
    market_policy: PerpsMarketPolicyV1
    occurrence: EconomicCommandOccurrenceV1
    module_input: PerpsMarginLaneModuleInputV1
    accepted: PerpsMarginAcceptedV1
    verified_price: VerifiedGlobalOraclePriceV1 | None

    def __post_init__(self) -> None:
        expected_types = (
            (self.profile, EconomicProfileSnapshotV1),
            (self.policy_registry, EconomicPolicyRegistryV1),
            (self.market_policy, PerpsMarketPolicyV1),
            (self.occurrence, EconomicCommandOccurrenceV1),
            (self.module_input, PerpsMarginLaneModuleInputV1),
            (self.accepted, PerpsMarginAcceptedV1),
        )
        if any(type(value) is not expected for value, expected in expected_types):
            raise TypeError("perps margin route binding requires exact typed inputs")
        if self.verified_price is not None and (
            type(self.verified_price) is not VerifiedGlobalOraclePriceV1
        ):
            raise TypeError("perps margin route binding price must be checker-verified")


def _require_perps_market_policy_binding_v1(
    candidate: PerpsMarginReleaseRouteBindingCandidateV1,
    module_input: PerpsMarginLaneModuleInputV1,
) -> None:
    policy = require_governed_perps_market_policy_v1(
        profile=candidate.profile,
        policy_registry=candidate.policy_registry,
        occurrence=candidate.occurrence,
        market_policy=candidate.market_policy,
    )
    exact_bindings: tuple[tuple[object, object, str], ...] = (
        (module_input.command.market_id, policy.market_id, "market policy market"),
        (module_input.pre_state.market_id, policy.market_id, "market policy state market"),
        (module_input.command.asset, policy.quote_asset, "market policy quote asset"),
        (
            module_input.pre_state.collateral_asset,
            policy.quote_asset,
            "market policy state quote asset",
        ),
    )
    if candidate.verified_price is not None:
        exact_bindings = (
            *exact_bindings,
            (
                candidate.verified_price.market_id,
                policy.market_id,
                "market policy Oracle market",
            ),
            (
                candidate.verified_price.base_asset,
                policy.base_asset,
                "market policy base asset",
            ),
            (
                candidate.verified_price.quote_asset,
                policy.quote_asset,
                "market policy Oracle quote asset",
            ),
            (
                candidate.verified_price.oracle_id,
                policy.oracle_id,
                "market policy Oracle id",
            ),
        )
    for actual, expected, label in exact_bindings:
        if actual != expected:
            raise ValueError(f"perps margin {label} mismatch")


def _perps_oracle_bindings_v1(
    oracle_policy_root: str,
    occurrence: EconomicCommandOccurrenceV1,
    module_input: PerpsMarginLaneModuleInputV1,
    verified_price: VerifiedGlobalOraclePriceV1,
) -> tuple[tuple[object, object, str], ...]:
    return (
        (
            module_input.context.oracle_authority_root,
            verified_price.oracle_authority_root,
            "Oracle authority root",
        ),
        (
            module_input.context.oracle_occurrence_root,
            verified_price.occurrence_root,
            "Oracle occurrence root",
        ),
        (
            module_input.context.oracle_price_e8,
            verified_price.price_e8,
            "Oracle price",
        ),
        (
            occurrence.occurrence_id,
            verified_price.command_occurrence_id,
            "Oracle command occurrence",
        ),
        (
            occurrence.route_release_id,
            verified_price.route_release_id,
            "Oracle route release",
        ),
        (
            occurrence.pre_state_root,
            verified_price.pre_state_root,
            "Oracle pre-state",
        ),
        (oracle_policy_root, verified_price.policy_root, "Oracle policy"),
        (module_input.command.market_id, verified_price.market_id, "Oracle market"),
        (module_input.pre_state.market_id, verified_price.market_id, "Oracle state market"),
        (
            module_input.command.asset,
            verified_price.quote_asset,
            "Oracle quote asset",
        ),
        (
            module_input.pre_state.collateral_asset,
            verified_price.quote_asset,
            "Oracle state quote asset",
        ),
    )


def _require_perps_oracle_price_binding_v1(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    module_input: PerpsMarginLaneModuleInputV1,
    verified_price: VerifiedGlobalOraclePriceV1 | None,
) -> None:
    if not module_input.context.has_oracle_authority:
        if verified_price is not None:
            raise ValueError("perps margin has unexpected Oracle price authority")
        return
    if verified_price is None or type(verified_price) is not VerifiedGlobalOraclePriceV1:
        raise ValueError("perps margin Oracle price authority is missing")
    route = profile.route_registry.route_for_command(
        occurrence.command_kind,
        claimed_route_release_id=occurrence.route_release_id,
    )
    for actual, expected, label in _perps_oracle_bindings_v1(
        route.oracle_policy_root,
        occurrence,
        module_input,
        verified_price,
    ):
        if actual != expected:
            raise ValueError(f"perps margin {label} mismatch")


def bind_perps_margin_lane_output_to_release_route_v1(
    candidate: PerpsMarginReleaseRouteBindingCandidateV1,
) -> ReleaseRouteBoundLaneTransitionV1:
    """Bind one accepted perps-margin output to command and Oracle authority."""

    if type(candidate) is not PerpsMarginReleaseRouteBindingCandidateV1:
        raise TypeError("perps margin route candidate must have the exact type")
    owned_input, expected = _recompute_perps_margin_accepted_v1(
        candidate.module_input,
        candidate.accepted,
    )
    _require_perps_market_policy_binding_v1(candidate, owned_input)
    _require_perps_oracle_price_binding_v1(
        candidate.profile,
        candidate.occurrence,
        owned_input,
        candidate.verified_price,
    )
    return _bind_candidate_v1(
        candidate.profile,
        candidate.occurrence,
        _BindingCandidateV1(
            owned_input.command.command_kind,
            owned_input.command.command_body_hash,
            expected.statement_root,
            PERPS_MARGIN_MODULE_SCHEMA_V1,
            owned_input.context,
            expected.module_journal,
        ),
    )


__all__ = [
    "RELEASE_ROUTE_BOUND_LANE_TRANSITION_SCHEMA_V1",
    "ReleaseRouteBoundLaneTransitionV1",
    "ManagedAssetLifecycleReleaseRouteBindingCandidateV1",
    "PerpsMarginReleaseRouteBindingCandidateV1",
    "bind_asset_transfer_lane_output_to_release_route_v1",
    "bind_managed_asset_lifecycle_lane_output_to_release_route_v1",
    "bind_perps_margin_lane_output_to_release_route_v1",
]
