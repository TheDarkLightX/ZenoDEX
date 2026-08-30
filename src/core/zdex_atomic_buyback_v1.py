"""Same-occurrence fee allocation, ZDEX purchase, and burn composition."""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from typing import Final

from .global_economic_proof_v1 import EconomicCommandOccurrenceV1, ReceiptKindV1
from .global_settlement_types_v1 import (
    MAX_DELTA_ATOMS_V1,
    MIN_DELTA_ATOMS_V1,
    ZERO_ROOT_V1,
    AssetConservationRowV1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    LaneWriteV1,
    ReleaseStatusV1,
    RouteReleaseV1,
    hash_global_v1,
)
from .zdex_atomic_buyback_state_v1 import ZDEXAtomicBuybackTokenomicsStateV1
from .zdex_buyback_spot_safety_receipt_v1 import (
    VerifiedZDEXBuybackSpotSafetyPurchaseV2,
)
from .zdex_fee_allocation_types_v1 import (
    FEE_BUYBACK_PRINCIPAL_V1,
)
from .zdex_hyperdeflation_results_v1 import (
    ZDEXPurchaseAndBurnAcceptedV1,
    ZDEXPurchaseAndBurnRejectedV1,
)
from .zdex_hyperdeflation_route_refinement_v1 import (
    ZDEXBurnLeafProjectionV1,
    refine_zdex_burn_leaf_v1,
)
from .zdex_hyperdeflation_types_v1 import (
    ZDEXAmountBucketV1,
    ZDEXBurnRouteContextV1,
    ZDEXHyperdeflationPolicyV1,
    ZDEXPurchaseAndBurnCommandV1,
    ZDEXSupplyStateV1,
)
from .zdex_hyperdeflation_v1 import transition_zdex_purchase_and_burn_v1
from .zdex_purchase_burn_effects_v1 import burn_effects_v1, purchase_effects_v2
from .zdex_purchase_burn_receipt_verification_v1 import (
    GovernedVerifiedZDEXAMMPurchaseV2,
    VerifiedZDEXBurnV1,
)
from .zdex_purchase_burn_route_types_v1 import (
    AMM_POOL_CUSTODY_DOMAIN_V1,
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    PROTOCOL_BUYBACK_CUSTODY_DOMAIN_V1,
    ZDEXAMMPurchaseJournalV2,
    ZDEXBuybackExecutionPolicyV1,
    zdex_occurrence_burn_port_v1,
    zdex_pool_reserve_principal_v1,
)
from .zdex_verified_buyback_spend_v1 import VerifiedZDEXBuybackSpendV1

ZDEX_ATOMIC_BUYBACK_PENDING_SCHEMA_V1: Final = "zenodex/zdex-atomic-buyback-pending/v1"
ZDEX_ATOMIC_BUYBACK_ACCEPTED_SCHEMA_V1: Final = "zenodex/zdex-atomic-buyback-accepted/v1"
_ACCEPTED_TOKEN = object()


def zdex_atomic_buyback_lane_coordination_obligation_root_v1(
    post_state: ZDEXAtomicBuybackTokenomicsStateV1,
    effects: GlobalEconomicEffectPlanV1,
    burn: ZDEXBurnLeafProjectionV1,
) -> str:
    """Name the remaining proof obligation after both module leaves verify."""

    if type(post_state) is not ZDEXAtomicBuybackTokenomicsStateV1:
        raise TypeError("atomic buyback obligation post-state must be exact typed data")
    if type(effects) is not GlobalEconomicEffectPlanV1:
        raise TypeError("atomic buyback obligation effects must be exact typed data")
    if type(burn) is not ZDEXBurnLeafProjectionV1:
        raise TypeError("atomic buyback obligation burn must be exact typed data")
    return hash_global_v1(
        "zdex-atomic-buyback-lane-coordination-obligation-v1",
        {
            "schema": ZDEX_ATOMIC_BUYBACK_ACCEPTED_SCHEMA_V1,
            "command_occurrence_id": burn.journal.command_occurrence_id,
            "burn_journal_root": burn.journal.journal_root,
            "effect_plan_root": effects.effect_plan_root,
            "post_tokenomics_state_root": post_state.state_root,
            "lane_writes": effects.lane_writes,
            "requirement": "VERIFIED_COMPLETE_LANE_ROOTS_AND_GLOBAL_REFINEMENT",
        },
    )


class ZDEXAtomicBuybackRejectCodeV1(str, Enum):
    ROUTE_MISMATCH = "ROUTE_MISMATCH"
    SPEND_MISMATCH = "SPEND_MISMATCH"
    PURCHASE_MISMATCH = "PURCHASE_MISMATCH"
    PURCHASE_WITNESS_MISMATCH = "PURCHASE_WITNESS_MISMATCH"
    TOKENOMICS_STATE_MISMATCH = "TOKENOMICS_STATE_MISMATCH"
    BURN_REJECTED = "BURN_REJECTED"
    BURN_WITNESS_MISMATCH = "BURN_WITNESS_MISMATCH"


@dataclass(frozen=True, slots=True)
class ZDEXAtomicBuybackCandidateV1:
    occurrence: EconomicCommandOccurrenceV1
    route: RouteReleaseV1
    safety_purchase: VerifiedZDEXBuybackSpotSafetyPurchaseV2
    verified_spend: VerifiedZDEXBuybackSpendV1
    purchase_journal: ZDEXAMMPurchaseJournalV2
    purchase_effects: GlobalEconomicEffectPlanV1
    verified_purchase: GovernedVerifiedZDEXAMMPurchaseV2
    hyperdeflation_policy: ZDEXHyperdeflationPolicyV1

    def __post_init__(self) -> None:
        expected = (
            (self.occurrence, EconomicCommandOccurrenceV1),
            (self.route, RouteReleaseV1),
            (self.safety_purchase, VerifiedZDEXBuybackSpotSafetyPurchaseV2),
            (self.verified_spend, VerifiedZDEXBuybackSpendV1),
            (self.purchase_journal, ZDEXAMMPurchaseJournalV2),
            (self.purchase_effects, GlobalEconomicEffectPlanV1),
            (self.verified_purchase, GovernedVerifiedZDEXAMMPurchaseV2),
            (self.hyperdeflation_policy, ZDEXHyperdeflationPolicyV1),
        )
        if any(type(value) is not kind for value, kind in expected):
            raise TypeError("atomic buyback candidate requires exact typed data")


@dataclass(frozen=True, slots=True)
class ZDEXAtomicBuybackRejectedV1:
    code: ZDEXAtomicBuybackRejectCodeV1
    pre_state: ZDEXAtomicBuybackTokenomicsStateV1
    post_state: ZDEXAtomicBuybackTokenomicsStateV1
    effects: GlobalEconomicEffectPlanV1 = GlobalEconomicEffectPlanV1.empty()

    def __post_init__(self) -> None:
        if type(self.code) is not ZDEXAtomicBuybackRejectCodeV1:
            raise TypeError("atomic buyback reject code is not closed")
        if self.pre_state is not self.post_state or not self.effects.is_empty:
            raise ValueError("atomic buyback rejection must be an exact no-effect no-op")


@dataclass(frozen=True, slots=True)
class ZDEXAtomicBuybackPendingV1:
    candidate: ZDEXAtomicBuybackCandidateV1
    occurrence: EconomicCommandOccurrenceV1
    route: RouteReleaseV1
    pre_state: ZDEXAtomicBuybackTokenomicsStateV1
    post_state: ZDEXAtomicBuybackTokenomicsStateV1
    purchase_journal: ZDEXAMMPurchaseJournalV2
    burn: ZDEXBurnLeafProjectionV1
    effects: GlobalEconomicEffectPlanV1
    pending_terminal_obligations_root: str

    def __post_init__(self) -> None:
        if self.pending_terminal_obligations_root == ZERO_ROOT_V1:
            raise ValueError("atomic buyback pending result must retain burn obligation")
        if self.burn.accepted.post_state != self.post_state.tokenomics.supply_state:
            raise ValueError("atomic buyback pending supply projection mismatch")


@dataclass(frozen=True, slots=True)
class _ZDEXAtomicBuybackAcceptedFieldsV1:
    pre_state: ZDEXAtomicBuybackTokenomicsStateV1
    post_state: ZDEXAtomicBuybackTokenomicsStateV1
    effects: GlobalEconomicEffectPlanV1
    burn: ZDEXBurnLeafProjectionV1
    verified_burn_binding_root: str
    pending_binding_root: str
    terminal_obligations_root: str


class ZDEXAtomicBuybackAcceptedV1:
    """Opaque module result constructed only after exact burn verification."""

    __slots__ = ("_fields",)
    _fields: _ZDEXAtomicBuybackAcceptedFieldsV1

    def __init__(
        self,
        token: object,
        fields: _ZDEXAtomicBuybackAcceptedFieldsV1,
    ) -> None:
        if token is not _ACCEPTED_TOKEN:
            raise TypeError("atomic buyback accepted result is verifier-constructed")
        if type(fields) is not _ZDEXAtomicBuybackAcceptedFieldsV1:
            raise TypeError("atomic buyback accepted fields are not closed")
        if fields.effects.is_empty:
            raise ValueError("atomic buyback accepted effects must be nonempty")
        if type(fields.verified_burn_binding_root) is not str or (
            fields.verified_burn_binding_root == ZERO_ROOT_V1
        ):
            raise ValueError("atomic buyback accepted burn binding must be nonzero")
        if type(fields.pending_binding_root) is not str or (
            fields.pending_binding_root == ZERO_ROOT_V1
        ):
            raise ValueError("atomic buyback accepted pending binding must be nonzero")
        if (
            fields.terminal_obligations_root
            != zdex_atomic_buyback_lane_coordination_obligation_root_v1(
                fields.post_state,
                fields.effects,
                fields.burn,
            )
        ):
            raise ValueError("atomic buyback result must retain lane coordination obligation")
        if fields.burn.accepted.post_state != fields.post_state.tokenomics.supply_state:
            raise ValueError("atomic buyback final supply projection mismatch")
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("atomic buyback accepted result is immutable")

    @property
    def pre_state(self) -> ZDEXAtomicBuybackTokenomicsStateV1:
        return self._fields.pre_state

    @property
    def post_state(self) -> ZDEXAtomicBuybackTokenomicsStateV1:
        return self._fields.post_state

    @property
    def effects(self) -> GlobalEconomicEffectPlanV1:
        return self._fields.effects

    @property
    def burn(self) -> ZDEXBurnLeafProjectionV1:
        return self._fields.burn

    @property
    def verified_burn_binding_root(self) -> str:
        return self._fields.verified_burn_binding_root

    @property
    def pending_binding_root(self) -> str:
        return self._fields.pending_binding_root

    @property
    def terminal_obligations_root(self) -> str:
        return self._fields.terminal_obligations_root


ZDEXAtomicBuybackPrepareResultV1 = ZDEXAtomicBuybackPendingV1 | ZDEXAtomicBuybackRejectedV1
ZDEXAtomicBuybackFinalizeResultV1 = ZDEXAtomicBuybackAcceptedV1 | ZDEXAtomicBuybackRejectedV1


def _reject(
    code: ZDEXAtomicBuybackRejectCodeV1,
    state: ZDEXAtomicBuybackTokenomicsStateV1,
) -> ZDEXAtomicBuybackRejectedV1:
    return ZDEXAtomicBuybackRejectedV1(code, state, state)


def _pending_binding_root_v1(pending: ZDEXAtomicBuybackPendingV1) -> str:
    return hash_global_v1(
        "zdex-atomic-buyback-pending-binding-v1",
        {
            "schema": ZDEX_ATOMIC_BUYBACK_PENDING_SCHEMA_V1,
            "command_occurrence_id": pending.occurrence.occurrence_id,
            "route_release_id": pending.route.route_release_id,
            "pre_tokenomics_state_root": pending.pre_state.state_root,
            "post_tokenomics_state_root": pending.post_state.state_root,
            "purchase_journal_root": pending.purchase_journal.journal_root,
            "burn_journal_root": pending.burn.journal.journal_root,
            "effect_plan_root": pending.effects.effect_plan_root,
            "pending_terminal_obligations_root": pending.pending_terminal_obligations_root,
        },
    )


def _witness_matches(
    witness: VerifiedZDEXBurnV1,
    *,
    route: RouteReleaseV1,
    occurrence: EconomicCommandOccurrenceV1,
    module_index: int,
    expected_writer_epoch: int,
    journal_root: str,
    effect_plan_root: str,
    authority_head_root: str,
    verifier_binding_root: str,
) -> bool:
    return (
        witness.route_release_id == route.route_release_id
        and witness.module_release_id == route.module_release_ids[module_index]
        and witness.command_occurrence_id == occurrence.occurrence_id
        and witness.profile_root == occurrence.profile_root
        and witness.writer_epoch == expected_writer_epoch
        and witness.journal_root == journal_root
        and witness.effect_plan_root == effect_plan_root
        and witness.receipt_kind is ReceiptKindV1.SUCCINCT
        and authority_head_root != ZERO_ROOT_V1
        and verifier_binding_root != ZERO_ROOT_V1
        and witness.authority_head_root == authority_head_root
        and witness.verifier_binding_root == verifier_binding_root
    )


def _governed_purchase_witness_matches_v2(
    witness: GovernedVerifiedZDEXAMMPurchaseV2,
    *,
    route: RouteReleaseV1,
    occurrence: EconomicCommandOccurrenceV1,
    expected_writer_epoch: int,
    journal_root: str,
    effect_plan_root: str,
    safety_purchase: VerifiedZDEXBuybackSpotSafetyPurchaseV2,
) -> bool:
    leaf = witness.verified_leaf
    return (
        leaf.route_release_id == route.route_release_id
        and leaf.module_release_id == route.module_release_ids[0]
        and leaf.command_occurrence_id == occurrence.occurrence_id
        and leaf.profile_root == occurrence.profile_root
        and leaf.writer_epoch == expected_writer_epoch
        and leaf.journal_root == journal_root
        and leaf.effect_plan_root == effect_plan_root
        and leaf.receipt_kind is ReceiptKindV1.SUCCINCT
        and leaf.expected_image_id == safety_purchase.expected_image_id
        and witness.price_authority_root == safety_purchase.price_authority_root
        and witness.authority_head_root == safety_purchase.authority_head_root
        and witness.verifier_binding_root == safety_purchase.verifier_binding_root
        and witness.policy_registry_root != ZERO_ROOT_V1
    )


def _intermediate_supply_v1(
    state: ZDEXSupplyStateV1,
    purchase: ZDEXAMMPurchaseJournalV2,
) -> ZDEXSupplyStateV1 | None:
    if (
        state.live_supply_atoms != purchase.zdex_supply_atoms
        or state.bucket_atoms(purchase.zdex_pool_bucket_id) != purchase.zdex_pool_pre_atoms
        or state.bucket_atoms(purchase.burn_bucket_id) is not None
    ):
        return None
    buckets = tuple(row for row in state.buckets if row.bucket_id != purchase.zdex_pool_bucket_id)
    if purchase.zdex_pool_post_atoms > 0:
        buckets = (
            *buckets,
            ZDEXAmountBucketV1(purchase.zdex_pool_bucket_id, purchase.zdex_pool_post_atoms),
        )
    buckets = (*buckets, ZDEXAmountBucketV1(purchase.burn_bucket_id, purchase.purchased_zdex_atoms))
    return replace(state, buckets=tuple(sorted(buckets, key=lambda row: row.bucket_id)))


def _aggregate_rows_v1(rows: tuple[EconomicEffectRowV1, ...]) -> tuple[EconomicEffectRowV1, ...]:
    totals: dict[tuple[str, str, str, str], tuple[EconomicEffectRowV1, int]] = {}
    for row in rows:
        exemplar, prior = totals.get(row.key, (row, 0))
        total = prior + row.delta_atoms
        if not MIN_DELTA_ATOMS_V1 <= total <= MAX_DELTA_ATOMS_V1:
            raise ValueError("atomic buyback aggregate effect exceeds i128")
        totals[row.key] = (exemplar, total)
    return tuple(
        EconomicEffectRowV1(row.kind, row.principal, row.asset, row.custody_domain, total)
        for _, (row, total) in sorted(totals.items())
        if total != 0
    )


def _fee_funded_purchase_rows_v1(
    candidate: ZDEXAtomicBuybackCandidateV1,
) -> tuple[EconomicEffectRowV1, ...]:
    """Preserve fee provenance while composing allocation and immediate spend."""

    allocation = candidate.verified_spend.accepted.fee_allocation
    purchase = candidate.purchase_journal
    buyback_allocated = allocation.occurrence.buyback_quote_atoms
    existing_buyback = allocation.pre_state.destination_balances[0].allocation_atoms
    spend_from_existing = min(purchase.quote_amount_in_atoms, existing_buyback)
    spend_from_new = purchase.quote_amount_in_atoms - spend_from_existing
    if spend_from_new > buyback_allocated:
        raise ValueError("atomic buyback spend exceeds available fee allocation")
    retained_new = buyback_allocated - spend_from_new
    rows: list[EconomicEffectRowV1] = []
    for row in allocation.effects.rows:
        if row.kind is not EconomicEffectKindV1.FEE_ALLOCATION:
            rows.append(row)
            continue
        if row.principal != FEE_BUYBACK_PRINCIPAL_V1:
            rows.extend(
                (
                    row,
                    EconomicEffectRowV1(
                        EconomicEffectKindV1.CUSTODY,
                        row.principal,
                        row.asset,
                        row.custody_domain,
                        row.delta_atoms,
                    ),
                )
            )
            continue
        for principal, domain, amount in (
            (
                FEE_BUYBACK_PRINCIPAL_V1,
                PROTOCOL_BUYBACK_CUSTODY_DOMAIN_V1,
                retained_new,
            ),
            (
                purchase.quote_pool_bucket_id,
                AMM_POOL_CUSTODY_DOMAIN_V1,
                spend_from_new,
            ),
        ):
            if amount == 0:
                continue
            rows.extend(
                (
                    EconomicEffectRowV1(
                        EconomicEffectKindV1.FEE_ALLOCATION,
                        principal,
                        row.asset,
                        domain,
                        amount,
                    ),
                    EconomicEffectRowV1(
                        EconomicEffectKindV1.CUSTODY,
                        principal,
                        row.asset,
                        domain,
                        amount,
                    ),
                )
            )
    for row in candidate.purchase_effects.rows:
        if (
            row.kind is EconomicEffectKindV1.CUSTODY
            and row.principal == purchase.quote_source_bucket_id
            and row.custody_domain == PROTOCOL_BUYBACK_CUSTODY_DOMAIN_V1
        ):
            if spend_from_existing:
                rows.append(replace(row, delta_atoms=-spend_from_existing))
        elif (
            row.kind is EconomicEffectKindV1.CUSTODY
            and row.principal == purchase.quote_pool_bucket_id
            and row.custody_domain == AMM_POOL_CUSTODY_DOMAIN_V1
        ):
            if spend_from_existing:
                rows.append(replace(row, delta_atoms=spend_from_existing))
        else:
            rows.append(row)
    return tuple(rows)


def _compose_effects_v1(
    candidate: ZDEXAtomicBuybackCandidateV1,
    post_state: ZDEXAtomicBuybackTokenomicsStateV1,
    burn: ZDEXBurnLeafProjectionV1,
) -> GlobalEconomicEffectPlanV1:
    allocation = candidate.verified_spend.accepted.fee_allocation
    purchase = candidate.purchase_journal
    pre_state = candidate.verified_spend.tokenomics_pre_state
    return GlobalEconomicEffectPlanV1(
        rows=_aggregate_rows_v1((*_fee_funded_purchase_rows_v1(candidate), *burn.effects.rows)),
        asset_conservation=tuple(
            sorted(
                (
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
                        pre_state.tokenomics.supply_state.live_supply_atoms,
                        post_state.tokenomics.supply_state.live_supply_atoms,
                        pre_state.tokenomics.supply_state.live_supply_atoms,
                        post_state.tokenomics.supply_state.live_supply_atoms,
                        0,
                        purchase.purchased_zdex_atoms,
                    ),
                ),
                key=lambda row: row.asset,
            )
        ),
        fee_conservation=allocation.effects.fee_conservation,
        lane_writes=(
            LaneWriteV1(
                LaneIdV1.SPOT_LIQUIDITY,
                purchase.pre_spot_lane_root,
                purchase.post_spot_lane_root,
            ),
            LaneWriteV1(
                LaneIdV1.ZDEX_TOKENOMICS,
                pre_state.state_root,
                post_state.state_root,
            ),
        ),
        occurrence_consumptions=(candidate.occurrence.occurrence_id,),
        external_outbox_enqueue=(),
    )


def prepare_zdex_atomic_buyback_v1(
    candidate: ZDEXAtomicBuybackCandidateV1,
) -> ZDEXAtomicBuybackPrepareResultV1:
    """Derive the only admissible post-state while retaining a burn obligation."""

    if type(candidate) is not ZDEXAtomicBuybackCandidateV1:
        raise TypeError("atomic buyback candidate must be exact typed data")
    pre_state = candidate.verified_spend.tokenomics_pre_state
    spend = candidate.verified_spend.accepted
    purchase = candidate.purchase_journal
    safety = candidate.safety_purchase.journal
    if (
        candidate.route.status is not ReleaseStatusV1.SHADOW
        or candidate.route.accepts_new_objects
        or candidate.route.command_kind != PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1
        or candidate.route.ordered_lanes
        != (LaneIdV1.SPOT_LIQUIDITY, LaneIdV1.ZDEX_TOKENOMICS)
        or candidate.route.route_release_id != candidate.occurrence.route_release_id
        or candidate.route.module_release_ids[0] != purchase.spot_module_release_id
        or candidate.route.issue_burn_policy_root != candidate.hyperdeflation_policy.policy_root
        or candidate.occurrence.consumed_object_ids
    ):
        return _reject(ZDEXAtomicBuybackRejectCodeV1.ROUTE_MISMATCH, pre_state)
    if (
        candidate.verified_spend.safety_receipt_binding_root
        != candidate.safety_purchase.binding_root
        or candidate.verified_spend.global_pre_state_root != candidate.occurrence.pre_state_root
        or safety.command_occurrence_id != candidate.occurrence.occurrence_id
    ):
        return _reject(ZDEXAtomicBuybackRejectCodeV1.SPEND_MISMATCH, pre_state)
    available = spend.fee_allocation.post_state.destination_balances[0].allocation_atoms
    fee_post = spend.fee_post_state.destination_balances[0].allocation_atoms
    execution_policy = ZDEXBuybackExecutionPolicyV1(
        safety.pool_id,
        safety.pool_definition_root,
        safety.quote_asset_id,
        safety.zdex_asset_id,
    )
    if (
        purchase.chain_id != candidate.occurrence.chain_id
        or purchase.deployment_root != candidate.occurrence.deployment_root
        or purchase.profile_root != candidate.occurrence.profile_root
        or purchase.route_release_id != candidate.route.route_release_id
        or purchase.command_occurrence_id != candidate.occurrence.occurrence_id
        or purchase.buyback_budget_occurrence_root != spend.intent.intent_root
        or purchase.buyback_execution_policy_root != execution_policy.policy_root
        or purchase.price_safety_policy_root != safety.oracle_policy_root
        or purchase.oracle_occurrence_root != safety.oracle_occurrence_root
        or purchase.oracle_observed_height != safety.oracle_observed_height
        or purchase.oracle_quote_numerator_atoms != safety.oracle_quote_numerator_atoms
        or purchase.oracle_zdex_denominator_atoms != safety.oracle_zdex_denominator_atoms
        or purchase.route_safe_quote_limit_atoms != safety.route_safe_quote_limit_atoms
        or purchase.minimum_output_atoms != safety.minimum_output_atoms
        or purchase.quote_asset_id != safety.quote_asset_id
        or purchase.zdex_asset_id != safety.zdex_asset_id
        or purchase.quote_pool_bucket_id
        != zdex_pool_reserve_principal_v1(
            pool_id=safety.pool_id,
            asset_id=safety.quote_asset_id,
        )
        or purchase.zdex_pool_bucket_id
        != zdex_pool_reserve_principal_v1(
            pool_id=safety.pool_id,
            asset_id=safety.zdex_asset_id,
        )
        or purchase.burn_bucket_id
        != zdex_occurrence_burn_port_v1(
            profile_root=candidate.occurrence.profile_root,
            route_release_id=candidate.route.route_release_id,
            command_occurrence_id=candidate.occurrence.occurrence_id,
        )
        or purchase.quote_amount_in_atoms != spend.intent.quote_spend_atoms
        or purchase.quote_amount_in_atoms != safety.quote_amount_in_atoms
        or purchase.purchased_zdex_atoms != safety.purchased_zdex_atoms
        or purchase.pre_spot_lane_root != safety.pre_spot_lane_root
        or purchase.post_spot_lane_root != safety.post_spot_lane_root
        or purchase.quote_source_bucket_id != FEE_BUYBACK_PRINCIPAL_V1
        or purchase.quote_source_pre_atoms != available
        or purchase.quote_source_post_atoms != fee_post
        or purchase.quote_owned_atoms != spend.fee_allocation.pre_state.owned_and_custodied_atoms
        or purchase.quote_supply_atoms != spend.fee_allocation.pre_state.supply_atoms
        or candidate.purchase_effects != purchase_effects_v2(purchase)
    ):
        return _reject(ZDEXAtomicBuybackRejectCodeV1.PURCHASE_MISMATCH, pre_state)
    if not _governed_purchase_witness_matches_v2(
        candidate.verified_purchase,
        route=candidate.route,
        occurrence=candidate.occurrence,
        expected_writer_epoch=safety.writer_epoch,
        journal_root=purchase.journal_root,
        effect_plan_root=candidate.purchase_effects.effect_plan_root,
        safety_purchase=candidate.safety_purchase,
    ):
        return _reject(
            ZDEXAtomicBuybackRejectCodeV1.PURCHASE_WITNESS_MISMATCH,
            pre_state,
        )
    intermediate = _intermediate_supply_v1(pre_state.tokenomics.supply_state, purchase)
    if intermediate is None:
        return _reject(
            ZDEXAtomicBuybackRejectCodeV1.TOKENOMICS_STATE_MISMATCH,
            pre_state,
        )
    context = ZDEXBurnRouteContextV1(
        candidate.route.route_release_id,
        candidate.hyperdeflation_policy.policy_root,
        purchase.journal_root,
        purchase.burn_bucket_id,
        purchase.purchased_zdex_atoms,
        0,
        intermediate.remaining_epoch_burn_cap_atoms,
        purchase.purchased_zdex_atoms,
        intermediate.burn_budget_epoch,
    )
    burn_result = transition_zdex_purchase_and_burn_v1(
        candidate.hyperdeflation_policy,
        intermediate,
        context,
        ZDEXPurchaseAndBurnCommandV1(
            intermediate.state_root,
            intermediate.precision_epoch,
            purchase.journal_root,
            purchase.burn_bucket_id,
            purchase.purchased_zdex_atoms,
        ),
    )
    if type(burn_result) is ZDEXPurchaseAndBurnRejectedV1:
        return _reject(ZDEXAtomicBuybackRejectCodeV1.BURN_REJECTED, pre_state)
    if type(burn_result) is not ZDEXPurchaseAndBurnAcceptedV1:
        raise TypeError("atomic buyback burn result is not closed")
    burn = refine_zdex_burn_leaf_v1(
        burn_result,
        purchase,
        candidate.route.module_release_ids[1],
    )
    spend_post = candidate.verified_spend.tokenomics_post_state
    post_state = replace(
        spend_post,
        tokenomics=replace(
            spend_post.tokenomics,
            supply_state=burn_result.post_state,
        ),
    )
    effects = _compose_effects_v1(candidate, post_state, burn)
    return ZDEXAtomicBuybackPendingV1(
        candidate,
        candidate.occurrence,
        candidate.route,
        pre_state,
        post_state,
        purchase,
        burn,
        effects,
        safety.terminal_obligations_root,
    )


def finalize_zdex_atomic_buyback_v1(
    pending: ZDEXAtomicBuybackPendingV1,
    verified_burn: VerifiedZDEXBurnV1,
) -> ZDEXAtomicBuybackFinalizeResultV1:
    """Close the purchased-ZDEX obligation only with the exact burn receipt."""

    if type(pending) is not ZDEXAtomicBuybackPendingV1:
        raise TypeError("atomic buyback pending result must be exact typed data")
    recomputed = prepare_zdex_atomic_buyback_v1(pending.candidate)
    if type(recomputed) is not ZDEXAtomicBuybackPendingV1 or recomputed != pending:
        return _reject(
            ZDEXAtomicBuybackRejectCodeV1.BURN_WITNESS_MISMATCH,
            pending.pre_state,
        )
    if type(verified_burn) is not VerifiedZDEXBurnV1 or not _witness_matches(
        verified_burn,
        route=pending.route,
        occurrence=pending.occurrence,
        module_index=1,
        expected_writer_epoch=pending.burn.journal.writer_epoch,
        journal_root=pending.burn.journal.journal_root,
        effect_plan_root=burn_effects_v1(pending.burn.journal).effect_plan_root,
        authority_head_root=pending.candidate.safety_purchase.authority_head_root,
        verifier_binding_root=pending.candidate.safety_purchase.verifier_binding_root,
    ):
        return _reject(
            ZDEXAtomicBuybackRejectCodeV1.BURN_WITNESS_MISMATCH,
            pending.pre_state,
        )
    return ZDEXAtomicBuybackAcceptedV1(
        _ACCEPTED_TOKEN,
        _ZDEXAtomicBuybackAcceptedFieldsV1(
            pre_state=pending.pre_state,
            post_state=pending.post_state,
            effects=pending.effects,
            burn=pending.burn,
            verified_burn_binding_root=verified_burn.binding_root,
            pending_binding_root=_pending_binding_root_v1(pending),
            terminal_obligations_root=zdex_atomic_buyback_lane_coordination_obligation_root_v1(
                pending.post_state,
                pending.effects,
                pending.burn,
            ),
        ),
    )


__all__ = [
    "ZDEXAtomicBuybackAcceptedV1",
    "ZDEXAtomicBuybackCandidateV1",
    "ZDEXAtomicBuybackFinalizeResultV1",
    "ZDEXAtomicBuybackPendingV1",
    "ZDEXAtomicBuybackPrepareResultV1",
    "ZDEXAtomicBuybackRejectCodeV1",
    "ZDEXAtomicBuybackRejectedV1",
    "finalize_zdex_atomic_buyback_v1",
    "prepare_zdex_atomic_buyback_v1",
    "zdex_atomic_buyback_lane_coordination_obligation_root_v1",
]
