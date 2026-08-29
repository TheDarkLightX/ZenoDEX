"""Pure two-lane composer for an authenticated ZDEX purchase and burn."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, replace

from .global_economic_capability_profile_binding_v1 import (
    snapshot_economic_policy_registry_v1,
)
from .global_economic_profile_snapshot_v1 import (
    _snapshot_coordinator_release_v1,
    _snapshot_lane_release_v1,
    _snapshot_route_release_v1,
    snapshot_economic_profile_v1,
)
from .global_economic_proof_v1 import EconomicCommandOccurrenceV1, ReceiptKindV1
from .global_economic_refinement_snapshot_v1 import (
    _require_exact_dataclass_scalars_v1,
    _snapshot_effect_plan_v1,
    _snapshot_occurrence_v1,
)
from .global_settlement_types_v1 import (
    MAX_DELTA_ATOMS_V1,
    MIN_DELTA_ATOMS_V1,
    AssetConservationRowV1,
    EconomicEffectRowV1,
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    GlobalEconomicEffectPlanV1,
    LaneCoordinatorReleaseV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    LaneWriteV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    RouteReleaseV1,
    _require_nonnegative_int,
    _require_root,
    canonical_global_bytes_v1,
    hash_global_v1,
)
from .zdex_fee_allocation_receipt_verification_v1 import (
    VerifiedZDEXFeeAllocationV1,
    _snapshot_fee_journal_v1,
    _snapshot_fee_policy_v1,
    _snapshot_fee_state_v1,
    _VerifiedZDEXFeeAllocationFieldsV1,
)
from .zdex_fee_allocation_v1 import (
    FEE_BUYBACK_PRINCIPAL_V1,
    ZDEXFeeAllocationAcceptedV1,
    ZDEXFeeAllocationCommandV1,
    ZDEXFeeAllocationContextV1,
    ZDEXFeeAllocationOccurrenceV1,
    ZDEXFeeAllocationPolicyV1,
    ZDEXFeeStateV1,
    candidate_zdex_fee_allocation_policy_v1,
    transition_zdex_fee_allocation_v1,
)
from .zdex_purchase_burn_receipt_verification_v1 import (
    VerifiedZDEXAMMPurchaseV1,
    VerifiedZDEXBurnV1,
    _snapshot_burn_journal_v1,
    _snapshot_purchase_journal_v1,
    _VerifiedZDEXLaneFieldsV1,
)
from .zdex_purchase_burn_route_types_v1 import (
    AMM_PURCHASE_OUTPUT_ROLE_V1,
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    ZDEX_BURN_INPUT_ROLE_V1,
    ZDEX_BUYBACK_EXECUTION_POLICY_KIND_V1,
    ZDEXAMMPurchaseJournalV1,
    ZDEXBurnJournalV1,
    ZDEXBuybackExecutionPolicyV1,
    ZDEXPurchaseBurnRouteRejectCodeV1,
    zdex_amm_purchase_port_schema_root_v1,
    zdex_burn_port_schema_root_v1,
    zdex_occurrence_burn_port_v1,
    zdex_pool_reserve_principal_v1,
)
from .zdex_tokenomics_lane_v1 import (
    zdex_tokenomics_complete_lane_obligation_root_v1,
)


@dataclass(frozen=True, slots=True)
class _GovernedZDEXPurchaseBurnRouteFieldsV1:
    profile: EconomicProfileSnapshotV1
    route_release: RouteReleaseV1
    purchase_module_release: LaneModuleReleaseV1
    burn_module_release: LaneModuleReleaseV1
    purchase_coordinator_release: LaneCoordinatorReleaseV1
    burn_coordinator_release: LaneCoordinatorReleaseV1
    policy_registry: EconomicPolicyRegistryV1
    buyback_execution_policy: ZDEXBuybackExecutionPolicyV1


class GovernedZDEXPurchaseBurnRouteV1:
    """Profile-selected SHADOW releases with no publication authority."""

    __slots__ = ("_fields", "_trusted_profile_id", "_trusted_authority_epoch")
    _fields: _GovernedZDEXPurchaseBurnRouteFieldsV1
    _trusted_profile_id: str
    _trusted_authority_epoch: int

    def __init__(
        self,
        token: object,
        fields: _GovernedZDEXPurchaseBurnRouteFieldsV1,
        trusted_profile_id: str,
        trusted_authority_epoch: int,
    ) -> None:
        if token is not _GOVERNED_PURCHASE_BURN_ROUTE_TOKEN:
            raise TypeError("governed ZDEX purchase-burn route is verifier-constructed")
        if type(trusted_profile_id) is not str or type(trusted_authority_epoch) is not int:
            raise TypeError(
                "governed ZDEX purchase-burn trusted profile anchor "
                "must be exact typed data"
            )
        object.__setattr__(self, "_fields", fields)
        object.__setattr__(self, "_trusted_profile_id", trusted_profile_id)
        object.__setattr__(self, "_trusted_authority_epoch", trusted_authority_epoch)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("governed ZDEX purchase-burn route is immutable")


_GOVERNED_PURCHASE_BURN_ROUTE_TOKEN = object()


class _GovernedZDEXPurchaseBurnAnchorMismatchV1(ValueError):
    """Internal signal for a retained wrapper whose trusted graph changed."""


def _trusted_purchase_burn_anchor_v1(
    governed: GovernedZDEXPurchaseBurnRouteV1,
) -> tuple[str, int]:
    if type(governed) is not GovernedZDEXPurchaseBurnRouteV1:
        raise TypeError("ZDEX purchase-burn governed route must be verifier-constructed")
    profile_id = governed._trusted_profile_id
    authority_epoch = governed._trusted_authority_epoch
    if type(profile_id) is not str or type(authority_epoch) is not int:
        raise TypeError(
            "ZDEX purchase-burn trusted profile anchor must be exact typed data"
        )
    return profile_id, authority_epoch


def _registered_buyback_route_v1(
    profile: EconomicProfileSnapshotV1,
) -> RouteReleaseV1:
    for route in profile.route_registry.routes:
        if route.command_kind == PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1:
            return route
    raise ValueError("ZDEX purchase-burn governed route is absent")


def _require_governed_route_shapes_v1(
    fields: _GovernedZDEXPurchaseBurnRouteFieldsV1,
) -> None:
    route = fields.route_release
    purchase = fields.purchase_module_release
    burn = fields.burn_module_release
    purchase_coordinator = fields.purchase_coordinator_release
    burn_coordinator = fields.burn_coordinator_release
    if route.status is not ReleaseStatusV1.SHADOW or route.accepts_new_objects:
        raise ValueError("ZDEX purchase-burn route must remain SHADOW")
    if (
        route.command_kind != PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1
        or route.ordered_lanes
        != (LaneIdV1.SPOT_LIQUIDITY, LaneIdV1.ZDEX_TOKENOMICS)
        or route.module_release_ids != (purchase.release_id, burn.release_id)
        or route.dependency_roles
        != (AMM_PURCHASE_OUTPUT_ROLE_V1, ZDEX_BURN_INPUT_ROLE_V1)
        or route.port_schema_roots
        != (
            zdex_amm_purchase_port_schema_root_v1(),
            zdex_burn_port_schema_root_v1(),
        )
    ):
        raise ValueError("ZDEX purchase-burn governed route shape mismatch")
    expected_releases = (
        (purchase, LaneIdV1.SPOT_LIQUIDITY),
        (burn, LaneIdV1.ZDEX_TOKENOMICS),
    )
    if any(
        release.status is not ReleaseStatusV1.SHADOW
        or release.accepts_new_objects
        or release.lane_id is not lane_id
        or PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1 not in release.command_variants
        for release, lane_id in expected_releases
    ):
        raise ValueError("ZDEX purchase-burn governed module release shape mismatch")
    expected_coordinators = (
        (purchase_coordinator, LaneIdV1.SPOT_LIQUIDITY),
        (burn_coordinator, LaneIdV1.ZDEX_TOKENOMICS),
    )
    if any(
        coordinator.status is not ReleaseStatusV1.SHADOW
        or coordinator.accepts_new_objects
        or coordinator.lane_id is not lane_id
        for coordinator, lane_id in expected_coordinators
    ):
        raise ValueError("ZDEX purchase-burn governed coordinator shape mismatch")


def bind_zdex_purchase_burn_shadow_profile_v1(
    *,
    expected_profile_id: str,
    expected_authority_epoch: int,
    profile: EconomicProfileSnapshotV1,
    policy_registry: EconomicPolicyRegistryV1,
    buyback_execution_policy: ZDEXBuybackExecutionPolicyV1,
) -> GovernedZDEXPurchaseBurnRouteV1:
    """Own and select the exact SHADOW route graph from a trusted anchor."""

    if type(expected_profile_id) is not str:
        raise ValueError("ZDEX purchase-burn expected profile mismatch")
    if type(expected_authority_epoch) is not int:
        raise ValueError("ZDEX purchase-burn expected authority epoch mismatch")
    owned_profile = snapshot_economic_profile_v1(profile)
    owned_policy_registry = snapshot_economic_policy_registry_v1(policy_registry)
    if type(buyback_execution_policy) is not ZDEXBuybackExecutionPolicyV1:
        raise TypeError("ZDEX buyback execution policy must be exact typed data")
    owned_execution_policy = replace(buyback_execution_policy)
    if expected_profile_id != owned_profile.profile_id:
        raise ValueError("ZDEX purchase-burn expected profile mismatch")
    if expected_authority_epoch != owned_profile.authority_epoch:
        raise ValueError("ZDEX purchase-burn expected authority epoch mismatch")
    if owned_profile.status is not ProfileStatusV1.SHADOW:
        raise ValueError("ZDEX purchase-burn profile must remain SHADOW")
    if owned_policy_registry.registry_root != owned_profile.policy_registry_root:
        raise ValueError("ZDEX buyback economic policy registry mismatch")
    execution_binding = owned_policy_registry.require_binding(
        policy_kind=ZDEX_BUYBACK_EXECUTION_POLICY_KIND_V1,
        command_kind=PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    )
    if execution_binding.policy_root != owned_execution_policy.policy_root:
        raise ValueError("ZDEX buyback execution policy binding mismatch")
    fields = _GovernedZDEXPurchaseBurnRouteFieldsV1(
        owned_profile,
        _registered_buyback_route_v1(owned_profile),
        owned_profile.lane_registry.release_for(LaneIdV1.SPOT_LIQUIDITY),
        owned_profile.lane_registry.release_for(LaneIdV1.ZDEX_TOKENOMICS),
        owned_profile.lane_coordinator_registry.release_for(
            LaneIdV1.SPOT_LIQUIDITY
        ),
        owned_profile.lane_coordinator_registry.release_for(
            LaneIdV1.ZDEX_TOKENOMICS
        ),
        owned_policy_registry,
        owned_execution_policy,
    )
    _require_governed_route_shapes_v1(fields)
    return GovernedZDEXPurchaseBurnRouteV1(
        _GOVERNED_PURCHASE_BURN_ROUTE_TOKEN,
        fields,
        expected_profile_id,
        expected_authority_epoch,
    )


def _snapshot_governed_route_v1(
    governed: GovernedZDEXPurchaseBurnRouteV1,
) -> GovernedZDEXPurchaseBurnRouteV1:
    if type(governed) is not GovernedZDEXPurchaseBurnRouteV1:
        raise TypeError("ZDEX purchase-burn governed route must be verifier-constructed")
    fields = governed._fields
    if type(fields) is not _GovernedZDEXPurchaseBurnRouteFieldsV1:
        raise TypeError("ZDEX purchase-burn governed fields must be exact typed data")
    if type(fields.profile) is not EconomicProfileSnapshotV1:
        raise TypeError("ZDEX purchase-burn governed profile must be exact typed data")
    if type(fields.policy_registry) is not EconomicPolicyRegistryV1:
        raise TypeError("ZDEX purchase-burn policy registry must be exact typed data")
    if type(fields.buyback_execution_policy) is not ZDEXBuybackExecutionPolicyV1:
        raise TypeError("ZDEX purchase-burn execution policy must be exact typed data")
    trusted_profile_id, trusted_authority_epoch = _trusted_purchase_burn_anchor_v1(
        governed
    )
    owned_profile = snapshot_economic_profile_v1(fields.profile)
    if (
        owned_profile.profile_id != trusted_profile_id
        or owned_profile.authority_epoch != trusted_authority_epoch
    ):
        raise _GovernedZDEXPurchaseBurnAnchorMismatchV1(
            "ZDEX purchase-burn trusted profile anchor changed"
        )
    owned = bind_zdex_purchase_burn_shadow_profile_v1(
        expected_profile_id=trusted_profile_id,
        expected_authority_epoch=trusted_authority_epoch,
        profile=owned_profile,
        policy_registry=fields.policy_registry,
        buyback_execution_policy=fields.buyback_execution_policy,
    )
    owned_fields = owned._fields
    if (
        _snapshot_route_release_v1(fields.route_release)
        != owned_fields.route_release
        or _snapshot_lane_release_v1(fields.purchase_module_release)
        != owned_fields.purchase_module_release
        or _snapshot_lane_release_v1(fields.burn_module_release)
        != owned_fields.burn_module_release
        or _snapshot_coordinator_release_v1(fields.purchase_coordinator_release)
        != owned_fields.purchase_coordinator_release
        or _snapshot_coordinator_release_v1(fields.burn_coordinator_release)
        != owned_fields.burn_coordinator_release
        or snapshot_economic_policy_registry_v1(fields.policy_registry)
        != owned_fields.policy_registry
        or replace(fields.buyback_execution_policy)
        != owned_fields.buyback_execution_policy
    ):
        raise _GovernedZDEXPurchaseBurnAnchorMismatchV1(
            "ZDEX purchase-burn governed selection changed"
        )
    return owned


@dataclass(frozen=True, slots=True)
class ZDEXPurchaseBurnRouteCandidateV1:
    governed_profile: GovernedZDEXPurchaseBurnRouteV1
    route_release: RouteReleaseV1
    purchase_module_release: LaneModuleReleaseV1
    burn_module_release: LaneModuleReleaseV1
    occurrence: EconomicCommandOccurrenceV1
    buyback_budget_occurrence: ZDEXFeeAllocationOccurrenceV1
    verified_buyback_budget: VerifiedZDEXFeeAllocationV1
    buyback_budget_policy: ZDEXFeeAllocationPolicyV1
    buyback_budget_pre_state: ZDEXFeeStateV1
    purchase_journal: ZDEXAMMPurchaseJournalV1
    purchase_effects: GlobalEconomicEffectPlanV1
    verified_purchase: VerifiedZDEXAMMPurchaseV1
    burn_journal: ZDEXBurnJournalV1
    burn_effects: GlobalEconomicEffectPlanV1
    verified_burn: VerifiedZDEXBurnV1

    def __post_init__(self) -> None:
        expected = (
            (
                self.governed_profile,
                GovernedZDEXPurchaseBurnRouteV1,
                "governed profile",
            ),
            (self.route_release, RouteReleaseV1, "route release"),
            (
                self.purchase_module_release,
                LaneModuleReleaseV1,
                "purchase module release",
            ),
            (
                self.burn_module_release,
                LaneModuleReleaseV1,
                "burn module release",
            ),
            (self.occurrence, EconomicCommandOccurrenceV1, "occurrence"),
            (
                self.buyback_budget_occurrence,
                ZDEXFeeAllocationOccurrenceV1,
                "buyback budget occurrence",
            ),
            (
                self.verified_buyback_budget,
                VerifiedZDEXFeeAllocationV1,
                "buyback budget witness",
            ),
            (
                self.buyback_budget_policy,
                ZDEXFeeAllocationPolicyV1,
                "buyback budget policy",
            ),
            (
                self.buyback_budget_pre_state,
                ZDEXFeeStateV1,
                "buyback budget pre-state",
            ),
            (self.purchase_journal, ZDEXAMMPurchaseJournalV1, "purchase journal"),
            (self.purchase_effects, GlobalEconomicEffectPlanV1, "purchase effects"),
            (self.verified_purchase, VerifiedZDEXAMMPurchaseV1, "purchase witness"),
            (self.burn_journal, ZDEXBurnJournalV1, "burn journal"),
            (self.burn_effects, GlobalEconomicEffectPlanV1, "burn effects"),
            (self.verified_burn, VerifiedZDEXBurnV1, "burn witness"),
        )
        for value, expected_type, label in expected:
            if type(value) is not expected_type:
                raise TypeError(f"ZDEX route {label} must be exact typed data")


def _require_exact_witness_fields_v1(
    witness: VerifiedZDEXAMMPurchaseV1
    | VerifiedZDEXBurnV1
    | VerifiedZDEXFeeAllocationV1,
    *,
    expected_type: type[object],
    name: str,
) -> None:
    fields = witness._fields
    if type(fields) is not expected_type:
        raise TypeError(f"ZDEX route {name} fields must be exact typed data")
    _require_exact_dataclass_scalars_v1(fields, name=name)


def _snapshot_route_candidate_v1(
    candidate: ZDEXPurchaseBurnRouteCandidateV1,
) -> ZDEXPurchaseBurnRouteCandidateV1:
    """Own and exact-check every structured value consumed by the composer."""

    if type(candidate) is not ZDEXPurchaseBurnRouteCandidateV1:
        raise TypeError("ZDEX purchase-burn route candidate must be exact typed data")
    candidate.__post_init__()
    _require_exact_witness_fields_v1(
        candidate.verified_purchase,
        expected_type=_VerifiedZDEXLaneFieldsV1,
        name="purchase witness",
    )
    _require_exact_witness_fields_v1(
        candidate.verified_burn,
        expected_type=_VerifiedZDEXLaneFieldsV1,
        name="burn witness",
    )
    _require_exact_witness_fields_v1(
        candidate.verified_buyback_budget,
        expected_type=_VerifiedZDEXFeeAllocationFieldsV1,
        name="buyback budget witness",
    )
    return replace(
        candidate,
        governed_profile=_snapshot_governed_route_v1(candidate.governed_profile),
        route_release=_snapshot_route_release_v1(candidate.route_release),
        purchase_module_release=_snapshot_lane_release_v1(
            candidate.purchase_module_release
        ),
        burn_module_release=_snapshot_lane_release_v1(candidate.burn_module_release),
        occurrence=_snapshot_occurrence_v1(candidate.occurrence),
        buyback_budget_occurrence=_snapshot_fee_journal_v1(
            candidate.buyback_budget_occurrence
        ),
        buyback_budget_policy=_snapshot_fee_policy_v1(
            candidate.buyback_budget_policy
        ),
        buyback_budget_pre_state=_snapshot_fee_state_v1(
            candidate.buyback_budget_pre_state
        ),
        purchase_journal=_snapshot_purchase_journal_v1(
            candidate.purchase_journal
        ),
        purchase_effects=_snapshot_effect_plan_v1(candidate.purchase_effects),
        burn_journal=_snapshot_burn_journal_v1(candidate.burn_journal),
        burn_effects=_snapshot_effect_plan_v1(candidate.burn_effects),
    )


@dataclass(frozen=True, slots=True)
class ZDEXPurchaseBurnRouteAcceptedV1:
    route_release_id: str
    command_occurrence_id: str
    profile_root: str
    writer_epoch: int
    ordered_lane_journal_roots: tuple[str, str]
    ordered_verified_binding_roots: tuple[str, str]
    verified_budget_binding_root: str
    buyback_execution_policy_root: str
    effects: GlobalEconomicEffectPlanV1
    terminal_obligations_root: str

    @property
    def composition_journal_v2(self) -> ZDEXPurchaseBurnRouteCompositionJournalV2:
        return ZDEXPurchaseBurnRouteCompositionJournalV2(
            schema=ZDEX_PURCHASE_BURN_ROUTE_COMPOSITION_SCHEMA_V2,
            route_release_id=self.route_release_id,
            command_occurrence_id=self.command_occurrence_id,
            profile_root=self.profile_root,
            writer_epoch=self.writer_epoch,
            ordered_lane_journal_roots=self.ordered_lane_journal_roots,
            ordered_verified_binding_roots=self.ordered_verified_binding_roots,
            verified_budget_binding_root=self.verified_budget_binding_root,
            buyback_execution_policy_root=self.buyback_execution_policy_root,
            effect_plan_root=self.effects.effect_plan_root,
            terminal_obligations_root=self.terminal_obligations_root,
        )


ZDEX_PURCHASE_BURN_ROUTE_COMPOSITION_SCHEMA_V2 = (
    "zenodex/zdex-purchase-burn-route-composition/v2"
)


@dataclass(frozen=True, slots=True)
class ZDEXPurchaseBurnRouteCompositionJournalV2:
    schema: str
    route_release_id: str
    command_occurrence_id: str
    profile_root: str
    writer_epoch: int
    ordered_lane_journal_roots: tuple[str, str]
    ordered_verified_binding_roots: tuple[str, str]
    verified_budget_binding_root: str
    buyback_execution_policy_root: str
    effect_plan_root: str
    terminal_obligations_root: str

    def __post_init__(self) -> None:
        if type(self.schema) is not str or self.schema != (
            ZDEX_PURCHASE_BURN_ROUTE_COMPOSITION_SCHEMA_V2
        ):
            raise ValueError("ZDEX route composition V2 schema mismatch")
        _require_nonnegative_int(
            self.writer_epoch,
            name="ZDEX route composition V2 writer epoch",
        )
        for field_name in (
            "route_release_id",
            "command_occurrence_id",
            "profile_root",
            "verified_budget_binding_root",
            "buyback_execution_policy_root",
            "effect_plan_root",
        ):
            value = getattr(self, field_name)
            if type(value) is not str:
                raise TypeError(
                    f"ZDEX route composition V2 {field_name} must be exact str"
                )
            _require_root(value, name=f"ZDEX route composition V2 {field_name}")
        if type(self.terminal_obligations_root) is not str:
            raise TypeError(
                "ZDEX route composition V2 terminal obligations must be exact str"
            )
        _require_root(
            self.terminal_obligations_root,
            name="ZDEX route composition V2 terminal obligations",
            allow_zero=True,
        )
        for field_name in (
            "ordered_lane_journal_roots",
            "ordered_verified_binding_roots",
        ):
            roots = getattr(self, field_name)
            if type(roots) is not tuple or len(roots) != 2:
                raise ValueError(
                    f"ZDEX route composition V2 {field_name} must have two roots"
                )
            for root in roots:
                if type(root) is not str:
                    raise TypeError(
                        f"ZDEX route composition V2 {field_name} must use exact str"
                    )
                _require_root(root, name=f"ZDEX route composition V2 {field_name}")

    @property
    def journal_root(self) -> str:
        return hash_global_v1(
            "zdex-purchase-burn-route-composition-v2",
            self.to_canonical(),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": self.schema,
            "route_release_id": self.route_release_id,
            "command_occurrence_id": self.command_occurrence_id,
            "profile_root": self.profile_root,
            "writer_epoch": self.writer_epoch,
            "ordered_lane_journal_roots": self.ordered_lane_journal_roots,
            "ordered_verified_binding_roots": self.ordered_verified_binding_roots,
            "verified_budget_binding_root": self.verified_budget_binding_root,
            "buyback_execution_policy_root": self.buyback_execution_policy_root,
            "effect_plan_root": self.effect_plan_root,
            "terminal_obligations_root": self.terminal_obligations_root,
        }


@dataclass(frozen=True, slots=True)
class ZDEXPurchaseBurnRouteRejectedV1:
    code: ZDEXPurchaseBurnRouteRejectCodeV1
    effects: GlobalEconomicEffectPlanV1 = GlobalEconomicEffectPlanV1.empty()

    def __post_init__(self) -> None:
        if type(self.code) is not ZDEXPurchaseBurnRouteRejectCodeV1:
            raise TypeError("ZDEX route reject code is not closed")
        if type(self.effects) is not GlobalEconomicEffectPlanV1 or not self.effects.is_empty:
            raise ValueError("ZDEX route rejection must carry no effects")


ZDEXPurchaseBurnRouteResultV1 = (
    ZDEXPurchaseBurnRouteAcceptedV1 | ZDEXPurchaseBurnRouteRejectedV1
)


@dataclass(frozen=True, slots=True)
class _WitnessExpectationV1:
    route_release_id: str
    module_release_id: str
    expected_image_id: str
    occurrence_id: str
    profile_root: str
    writer_epoch: int


def _reject(code: ZDEXPurchaseBurnRouteRejectCodeV1) -> ZDEXPurchaseBurnRouteRejectedV1:
    return ZDEXPurchaseBurnRouteRejectedV1(code)


def _witness_matches(
    witness: VerifiedZDEXAMMPurchaseV1 | VerifiedZDEXBurnV1,
    *,
    expected: _WitnessExpectationV1,
    journal: ZDEXAMMPurchaseJournalV1 | ZDEXBurnJournalV1,
    effects: GlobalEconomicEffectPlanV1,
) -> bool:
    journal_bytes = canonical_global_bytes_v1(journal)
    return (
        witness.route_release_id == expected.route_release_id
        and witness.module_release_id == expected.module_release_id
        and witness.expected_image_id == expected.expected_image_id
        and witness.command_occurrence_id == expected.occurrence_id
        and witness.profile_root == expected.profile_root
        and witness.writer_epoch == expected.writer_epoch
        and witness.journal_root == journal.journal_root
        and witness.journal_digest == "0x" + hashlib.sha256(journal_bytes).hexdigest()
        and witness.effect_plan_root == effects.effect_plan_root
        and witness.receipt_kind is ReceiptKindV1.SUCCINCT
    )


def _checked_delta(value: int) -> int:
    if not MIN_DELTA_ATOMS_V1 <= value <= MAX_DELTA_ATOMS_V1:
        raise ValueError("ZDEX route aggregate effect exceeds signed 128-bit atoms")
    return value


def _compose_rows(
    purchase: GlobalEconomicEffectPlanV1,
    burn: GlobalEconomicEffectPlanV1,
) -> tuple[EconomicEffectRowV1, ...]:
    totals: dict[tuple[str, str, str, str], tuple[EconomicEffectRowV1, int]] = {}
    for plan in (purchase, burn):
        for row in plan.rows:
            exemplar, prior = totals.get(row.key, (row, 0))
            totals[row.key] = (exemplar, _checked_delta(prior + row.delta_atoms))
    return tuple(
        EconomicEffectRowV1(
            exemplar.kind,
            exemplar.principal,
            exemplar.asset,
            exemplar.custody_domain,
            total,
        )
        for _, (exemplar, total) in sorted(totals.items())
        if total != 0
    )


def _compose_conservation(
    purchase: ZDEXAMMPurchaseJournalV1,
    burn: ZDEXBurnJournalV1,
) -> tuple[AssetConservationRowV1, ...]:
    rows = (
        AssetConservationRowV1(
            purchase.quote_asset_id,
            purchase.quote_owned_atoms,
            purchase.quote_owned_atoms,
            purchase.quote_supply_atoms,
            purchase.quote_supply_atoms,
            0,
            0,
        ),
        AssetConservationRowV1(
            purchase.zdex_asset_id,
            purchase.zdex_owned_atoms,
            burn.zdex_owned_post_atoms,
            purchase.zdex_supply_atoms,
            burn.zdex_supply_post_atoms,
            0,
            burn.burned_zdex_atoms,
        ),
    )
    return tuple(sorted(rows, key=lambda row: row.asset))


def _compose_effects(
    candidate: ZDEXPurchaseBurnRouteCandidateV1,
) -> GlobalEconomicEffectPlanV1:
    purchase = candidate.purchase_journal
    burn = candidate.burn_journal
    return GlobalEconomicEffectPlanV1(
        rows=_compose_rows(candidate.purchase_effects, candidate.burn_effects),
        asset_conservation=_compose_conservation(purchase, burn),
        fee_conservation=(),
        lane_writes=(
            LaneWriteV1(
                LaneIdV1.SPOT_LIQUIDITY,
                purchase.pre_spot_lane_root,
                purchase.post_spot_lane_root,
            ),
        ),
        occurrence_consumptions=(candidate.occurrence.occurrence_id,),
        external_outbox_enqueue=(),
    )


def _budget_bindings_match(
    candidate: ZDEXPurchaseBurnRouteCandidateV1,
    occurrence_id: str,
) -> bool:
    occurrence = candidate.occurrence
    purchase = candidate.purchase_journal
    burn = candidate.burn_journal
    budget = candidate.buyback_budget_occurrence
    budget_root = budget.occurrence_root
    return not any(
        (
            budget.chain_id != occurrence.chain_id,
            budget.deployment_root != occurrence.deployment_root,
            budget.profile_root != occurrence.profile_root,
            budget.writer_epoch != purchase.writer_epoch,
            budget.authorized_buyback_route_release_id
            != candidate.route_release.route_release_id,
            budget.tokenomics_module_release_id != burn.tokenomics_module_release_id,
            budget.command_occurrence_id == occurrence_id,
            budget_root == occurrence_id,
            occurrence.consumed_object_ids != (budget_root,),
            purchase.quote_source_bucket_id != FEE_BUYBACK_PRINCIPAL_V1,
        )
    )


def _budget_witness_matches(
    candidate: ZDEXPurchaseBurnRouteCandidateV1,
    tokenomics_release: LaneModuleReleaseV1,
) -> bool:
    route = candidate.route_release
    occurrence = candidate.occurrence
    purchase = candidate.purchase_journal
    burn = candidate.burn_journal
    budget = candidate.buyback_budget_occurrence
    witness = candidate.verified_buyback_budget
    journal_digest = "0x" + hashlib.sha256(
        canonical_global_bytes_v1(budget)
    ).hexdigest()
    return not any(
        (
            witness.authorized_buyback_route_release_id != route.route_release_id,
            witness.allocation_route_release_id
            != budget.allocation_route_release_id,
            witness.module_release_id != burn.tokenomics_module_release_id,
            witness.expected_image_id != tokenomics_release.guest_image_id,
            witness.command_occurrence_id != budget.command_occurrence_id,
            witness.profile_root != occurrence.profile_root,
            witness.writer_epoch != purchase.writer_epoch,
            witness.journal_root != budget.occurrence_root,
            witness.journal_digest != journal_digest,
            witness.effect_plan_root != budget.effect_plan_root,
            witness.policy_root != budget.policy_root,
            witness.fee_asset_id != budget.fee_asset_id,
            witness.fee_ingress_atoms != budget.fee_charged_atoms,
            witness.buyback_quote_atoms != budget.buyback_quote_atoms,
            witness.pre_lane_root != budget.pre_lane_root,
            witness.post_lane_root != budget.post_lane_root,
            witness.receipt_kind is not ReceiptKindV1.SUCCINCT,
        )
    )


def _budget_allocation_recomputes(
    candidate: ZDEXPurchaseBurnRouteCandidateV1,
) -> bool:
    budget = candidate.buyback_budget_occurrence
    policy = candidate.buyback_budget_policy
    if policy != candidate_zdex_fee_allocation_policy_v1():
        return False
    context = ZDEXFeeAllocationContextV1(
        chain_id=budget.chain_id,
        deployment_root=budget.deployment_root,
        profile_root=budget.profile_root,
        writer_epoch=budget.writer_epoch,
        allocation_route_release_id=budget.allocation_route_release_id,
        authorized_buyback_route_release_id=(
            budget.authorized_buyback_route_release_id
        ),
        tokenomics_module_release_id=budget.tokenomics_module_release_id,
        command_occurrence_id=budget.command_occurrence_id,
        policy_root=budget.policy_root,
    )
    recomputed = transition_zdex_fee_allocation_v1(
        context,
        candidate.buyback_budget_pre_state,
        policy,
        ZDEXFeeAllocationCommandV1(budget.fee_charged_atoms),
    )
    return (
        type(recomputed) is ZDEXFeeAllocationAcceptedV1
        and recomputed.occurrence == budget
    )


def _binding_reject_code(
    candidate: ZDEXPurchaseBurnRouteCandidateV1,
    occurrence_id: str,
    purchase_release: LaneModuleReleaseV1,
    burn_release: LaneModuleReleaseV1,
) -> ZDEXPurchaseBurnRouteRejectCodeV1 | None:
    route = candidate.route_release
    occurrence = candidate.occurrence
    purchase = candidate.purchase_journal
    burn = candidate.burn_journal
    if (
        route.ordered_lanes
        != (LaneIdV1.SPOT_LIQUIDITY, LaneIdV1.ZDEX_TOKENOMICS)
        or route.module_release_ids
        != (purchase_release.release_id, burn_release.release_id)
        or purchase_release.lane_id is not LaneIdV1.SPOT_LIQUIDITY
        or burn_release.lane_id is not LaneIdV1.ZDEX_TOKENOMICS
        or purchase.spot_module_release_id != purchase_release.release_id
        or burn.tokenomics_module_release_id != burn_release.release_id
        or route.route_release_id != occurrence.route_release_id
        or route.route_release_id != purchase.route_release_id
        or route.route_release_id != burn.route_release_id
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.ROUTE_BINDING_MISMATCH
    if purchase.command_occurrence_id != occurrence_id or burn.command_occurrence_id != occurrence_id:
        return ZDEXPurchaseBurnRouteRejectCodeV1.OCCURRENCE_MISMATCH
    if (
        purchase.profile_root != occurrence.profile_root
        or burn.profile_root != occurrence.profile_root
        or purchase.writer_epoch != burn.writer_epoch
        or purchase.chain_id != occurrence.chain_id
        or burn.chain_id != occurrence.chain_id
        or purchase.deployment_root != occurrence.deployment_root
        or burn.deployment_root != occurrence.deployment_root
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.PROFILE_OR_EPOCH_MISMATCH
    if not _budget_bindings_match(candidate, occurrence_id):
        return ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_BUDGET_MISMATCH
    if not _budget_witness_matches(candidate, burn_release):
        return ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_BUDGET_MISMATCH
    if not _budget_allocation_recomputes(candidate):
        return ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_BUDGET_MISMATCH
    purchase_expected = _WitnessExpectationV1(
        route.route_release_id,
        purchase_release.release_id,
        purchase_release.guest_image_id,
        occurrence_id,
        occurrence.profile_root,
        purchase.writer_epoch,
    )
    if not _witness_matches(
        candidate.verified_purchase,
        expected=purchase_expected,
        journal=purchase,
        effects=candidate.purchase_effects,
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.PURCHASE_WITNESS_MISMATCH
    burn_expected = _WitnessExpectationV1(
        route.route_release_id,
        burn_release.release_id,
        burn_release.guest_image_id,
        occurrence_id,
        occurrence.profile_root,
        purchase.writer_epoch,
    )
    if not _witness_matches(
        candidate.verified_burn,
        expected=burn_expected,
        journal=burn,
        effects=candidate.burn_effects,
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.BURN_WITNESS_MISMATCH
    return None


def _governed_profile_reject_code(
    candidate: ZDEXPurchaseBurnRouteCandidateV1,
) -> ZDEXPurchaseBurnRouteRejectCodeV1 | None:
    fields = candidate.governed_profile._fields
    profile = fields.profile
    occurrence = candidate.occurrence
    purchase = candidate.purchase_journal
    if (
        candidate.route_release != fields.route_release
        or candidate.purchase_module_release != fields.purchase_module_release
        or candidate.burn_module_release != fields.burn_module_release
        or occurrence.profile_root != profile.profile_id
        or occurrence.route_release_id != fields.route_release.route_release_id
        or occurrence.command_kind != fields.route_release.command_kind
        or purchase.writer_epoch != profile.authority_epoch
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.GOVERNED_PROFILE_MISMATCH
    return None


def _economic_reject_code(
    candidate: ZDEXPurchaseBurnRouteCandidateV1,
) -> ZDEXPurchaseBurnRouteRejectCodeV1 | None:
    purchase = candidate.purchase_journal
    burn = candidate.burn_journal
    budget = candidate.buyback_budget_occurrence
    execution_policy = candidate.governed_profile._fields.buyback_execution_policy
    expected_quote_pool_bucket = zdex_pool_reserve_principal_v1(
        pool_id=execution_policy.pool_id,
        asset_id=execution_policy.quote_asset_id,
    )
    expected_zdex_pool_bucket = zdex_pool_reserve_principal_v1(
        pool_id=execution_policy.pool_id,
        asset_id=execution_policy.zdex_asset_id,
    )
    expected_burn_bucket = zdex_occurrence_burn_port_v1(
        profile_root=candidate.occurrence.profile_root,
        route_release_id=candidate.route_release.route_release_id,
        command_occurrence_id=candidate.occurrence.occurrence_id,
    )
    if (
        purchase.quote_asset_id != execution_policy.quote_asset_id
        or purchase.zdex_asset_id != execution_policy.zdex_asset_id
        or purchase.quote_pool_bucket_id != expected_quote_pool_bucket
        or purchase.zdex_pool_bucket_id != expected_zdex_pool_bucket
        or purchase.burn_bucket_id != expected_burn_bucket
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_EXECUTION_POLICY_MISMATCH
    if purchase.zdex_asset_id != burn.zdex_asset_id:
        return ZDEXPurchaseBurnRouteRejectCodeV1.ASSET_MISMATCH
    if burn.purchase_occurrence_root != purchase.journal_root:
        return ZDEXPurchaseBurnRouteRejectCodeV1.PURCHASE_OCCURRENCE_MISMATCH
    if purchase.purchased_zdex_atoms != burn.burned_zdex_atoms:
        return ZDEXPurchaseBurnRouteRejectCodeV1.AMOUNT_MISMATCH
    if (
        purchase.burn_bucket_id != burn.burn_bucket_id
        or purchase.burn_bucket_post_atoms != burn.burn_bucket_pre_atoms
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.BURN_BUCKET_MISMATCH
    if (
        purchase.buyback_budget_occurrence_root != budget.occurrence_root
        or burn.buyback_budget_occurrence_root != budget.occurrence_root
        or purchase.quote_asset_id != budget.fee_asset_id
        or purchase.quote_amount_in_atoms != burn.authorized_quote_input_atoms
        or purchase.quote_amount_in_atoms != budget.buyback_quote_atoms
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_BUDGET_MISMATCH
    if (
        purchase.zdex_owned_atoms != burn.zdex_owned_pre_atoms
        or purchase.zdex_supply_atoms != burn.zdex_supply_pre_atoms
        or purchase.quote_owned_atoms != purchase.quote_supply_atoms
        or purchase.zdex_owned_atoms != purchase.zdex_supply_atoms
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.CONSERVATION_HISTORY_DISCONNECTED
    return None


def compose_zdex_purchase_burn_route_v1(
    candidate: ZDEXPurchaseBurnRouteCandidateV1,
) -> ZDEXPurchaseBurnRouteResultV1:
    """Pair two verified leaf outputs and derive one exact route effect plan."""

    try:
        candidate = _snapshot_route_candidate_v1(candidate)
    except _GovernedZDEXPurchaseBurnAnchorMismatchV1:
        return _reject(ZDEXPurchaseBurnRouteRejectCodeV1.GOVERNED_PROFILE_MISMATCH)
    route = candidate.route_release
    purchase_release = candidate.purchase_module_release
    burn_release = candidate.burn_module_release
    occurrence = candidate.occurrence
    purchase = candidate.purchase_journal
    occurrence_id = occurrence.occurrence_id
    reject_code = _governed_profile_reject_code(candidate)
    if reject_code is not None:
        return _reject(reject_code)
    reject_code = _binding_reject_code(
        candidate,
        occurrence_id,
        purchase_release,
        burn_release,
    )
    if reject_code is not None:
        return _reject(reject_code)
    reject_code = _economic_reject_code(candidate)
    if reject_code is not None:
        return _reject(reject_code)

    burn = candidate.burn_journal

    effects = _compose_effects(candidate)
    return ZDEXPurchaseBurnRouteAcceptedV1(
        route.route_release_id,
        occurrence_id,
        occurrence.profile_root,
        purchase.writer_epoch,
        (purchase.journal_root, burn.journal_root),
        (
            candidate.verified_purchase.binding_root,
            candidate.verified_burn.binding_root,
        ),
        candidate.verified_buyback_budget.binding_root,
        candidate.governed_profile._fields.buyback_execution_policy.policy_root,
        effects,
        zdex_tokenomics_complete_lane_obligation_root_v1(),
    )


__all__ = [
    "GovernedZDEXPurchaseBurnRouteV1",
    "ZDEXPurchaseBurnRouteAcceptedV1",
    "ZDEXPurchaseBurnRouteCandidateV1",
    "ZDEXPurchaseBurnRouteCompositionJournalV2",
    "ZDEXPurchaseBurnRouteRejectedV1",
    "ZDEXPurchaseBurnRouteResultV1",
    "bind_zdex_purchase_burn_shadow_profile_v1",
    "compose_zdex_purchase_burn_route_v1",
]
