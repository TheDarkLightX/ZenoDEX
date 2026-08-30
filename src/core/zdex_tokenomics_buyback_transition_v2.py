"""Tokenomics successor that consumes one exact Spot V2 burn obligation.

Phase A remains the V1 fee-allocation and governed-spend kernel. Phase B binds
the exact V2 quote port and shared occurrence coordinates, then burns exactly
the purchased ZDEX atoms under the V1 retained-supply and epoch-cap rules.

This SHADOW leaf validates structure and cross-lane data consistency. Spot
execution provenance, Spot release selection, and permission to apply effects
belong to the authenticated route composer and settlement verifier.
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace
from typing import Final, TypeAlias

from . import zdex_tokenomics_buyback_transition_v1 as tokenomics_v1
from .global_settlement_types_v1 import (
    GlobalEconomicEffectPlanV1,
    _require_atoms_u128,
    _require_nonnegative_int,
    _require_root,
    hash_global_v1,
)
from .zdex_atomic_buyback_quote_port_v2 import ZDEXAtomicBuybackQuotePortV2
from .zdex_buyback_spend_v1 import ZDEXBuybackSpendRejectCodeV1
from .zdex_fee_allocation_types_v1 import ZDEXFeeAllocationRejectCodeV1
from .zdex_purchase_burn_route_types_v1 import (
    zdex_occurrence_burn_port_v1,
    zdex_pool_reserve_principal_v1,
)
from .zdex_spot_buyback_transition_v1 import ZDEXSpotFlowRoleV1
from .zdex_spot_buyback_transition_v2 import (
    ZDEXSpotBuybackContextV2,
    ZDEXSpotFlowIdentityV2,
    ZDEXSpotTerminalObligationV2,
)
from .zdex_tokenomics_lane_v1 import (
    zdex_tokenomics_complete_lane_obligation_root_v1,
)

ZDEX_TOKENOMICS_PRIVATE_PORTS_SCHEMA_V2: Final = (
    "zenodex/zdex-tokenomics-private-ports/v2"
)
ZDEX_TOKENOMICS_TRANSITION_JOURNAL_SCHEMA_V2: Final = (
    "zenodex/zdex-tokenomics-buyback-transition-journal/v2"
)

_ACCEPTED_TOKEN_V2 = object()


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsBuybackInputV2:
    """Exact Phase-A input plus an untrusted Spot V2 terminal value."""

    intent_input: tokenomics_v1.ZDEXTokenomicsBuybackIntentInputV1
    spot_obligation: object

    def __post_init__(self) -> None:
        if type(self.intent_input) is not tokenomics_v1.ZDEXTokenomicsBuybackIntentInputV1:
            raise TypeError("Tokenomics V2 input requires an exact intent input")
        self.intent_input.__post_init__()


def _shared_occurrence_matches_v2(
    context: ZDEXSpotBuybackContextV2,
    authority: tokenomics_v1.ZDEXTokenomicsBuybackAuthorityContextV1,
    quote: ZDEXAtomicBuybackQuotePortV2,
    oracle_occurrence_id: str,
) -> bool:
    """Compare every Spot context coordinate owned by Tokenomics or the port."""

    coordinates = context.coordinates
    return (
        coordinates.profile_root == authority.profile_root
        and coordinates.route_release_id == authority.route_release_id
        and coordinates.command_occurrence_id == authority.command_occurrence_id
        and coordinates.global_pre_state_root == authority.global_pre_state_root
        and coordinates.producer_quote_pre_state_root
        == quote.producer_quote_pre_state_root
        and coordinates.producer_quote_post_state_root
        == quote.producer_quote_post_state_root
        and coordinates.producer_quote_effect_plan_root
        == quote.producer_quote_effect_plan_root
        and coordinates.quote_port_root == quote.port_root
        and context.chain_id == authority.chain_id
        and context.deployment_root == authority.deployment_root
        and context.writer_epoch == authority.writer_epoch
        and context.current_height == authority.current_height
        and context.spot_module_release_id == authority.spot_module_release_id
        and context.tokenomics_module_release_id
        == authority.tokenomics_module_release_id
        and context.execution_policy_root == authority.execution_policy.policy_root
        and context.price_policy_root == authority.price_policy_root
        and context.oracle_occurrence_id == oracle_occurrence_id
    )


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsPrivatePortsV2:
    """One produced quote port paired with one consumed V2 burn obligation."""

    quote_output: ZDEXAtomicBuybackQuotePortV2
    burn_input: ZDEXSpotTerminalObligationV2

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        if type(self.quote_output) is not ZDEXAtomicBuybackQuotePortV2:
            raise TypeError("Tokenomics V2 quote output must be exact typed data")
        if type(self.burn_input) is not ZDEXSpotTerminalObligationV2:
            raise TypeError("Tokenomics V2 burn input must be an exact V2 obligation")
        self.quote_output.validate()
        self.burn_input.validate()
        coordinates = self.burn_input.context.coordinates
        if (
            coordinates.quote_port_root != self.quote_output.port_root
            or coordinates.profile_root != self.quote_output.profile_root
            or coordinates.route_release_id != self.quote_output.route_release_id
            or coordinates.command_occurrence_id
            != self.quote_output.command_occurrence_id
            or coordinates.global_pre_state_root
            != self.quote_output.global_pre_state_root
            or coordinates.producer_quote_pre_state_root
            != self.quote_output.producer_quote_pre_state_root
            or coordinates.producer_quote_post_state_root
            != self.quote_output.producer_quote_post_state_root
            or coordinates.producer_quote_effect_plan_root
            != self.quote_output.producer_quote_effect_plan_root
            or self.burn_input.selected_pool_id
            != self.quote_output.selected_pool_id
            or self.burn_input.context.spot_module_release_id
            != self.quote_output.consumer_module_release_id
            or self.burn_input.consumer_module_release_id
            != self.quote_output.producer_module_release_id
        ):
            raise ValueError("Tokenomics V2 private ports are not one occurrence pair")

    @property
    def ports_root(self) -> str:
        self.validate()
        return hash_global_v1("zdex-tokenomics-private-ports-v2", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        self.validate()
        return {
            "schema": ZDEX_TOKENOMICS_PRIVATE_PORTS_SCHEMA_V2,
            "quote_port_root": self.quote_output.port_root,
            "burn_input_obligation_id": self.burn_input.obligation_id,
            "spot_context_root": self.burn_input.context.context_root,
            "spot_coordinates_root": self.burn_input.context.coordinates.coordinates_root,
            "quote_amount_atoms": self.quote_output.amount_atoms,
            "burn_amount_atoms": self.burn_input.purchased_atoms,
        }


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsBuybackJournalV2:
    """V2 public accounting witness and exact Spot-terminal discharge binding."""

    context_root: str
    pre_state_root: str
    spend_post_state_root: str
    post_state_root: str
    spend_effect_plan_root: str
    effect_plan_root: str
    quote_port_root: str
    private_ports_root: str
    discharged_obligation_id: str
    spot_context_root: str
    spot_coordinates_root: str
    spot_post_state_root: str
    lane_coordination_obligation_root: str
    fee_allocation_occurrence_root: str
    spend_intent_root: str
    safety_limit_binding_root: str
    selected_pool_id: str
    quote_asset_id: str
    zdex_asset_id: str
    current_height: int
    fee_charged_atoms: int
    buyback_allocation_atoms: int
    other_allocations_atoms: int
    carried_residue_atoms: int
    buyback_reserve_pre_atoms: int
    buyback_reserve_post_atoms: int
    quote_spend_atoms: int
    route_safe_quote_limit_atoms: int
    purchased_zdex_atoms: int
    burned_zdex_atoms: int
    live_supply_pre_atoms: int
    live_supply_post_atoms: int
    retained_supply_atoms: int
    remaining_epoch_burn_cap_pre_atoms: int
    remaining_epoch_burn_cap_post_atoms: int

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        for name in (
            "context_root",
            "pre_state_root",
            "spend_post_state_root",
            "post_state_root",
            "spend_effect_plan_root",
            "effect_plan_root",
            "quote_port_root",
            "private_ports_root",
            "discharged_obligation_id",
            "spot_context_root",
            "spot_coordinates_root",
            "spot_post_state_root",
            "lane_coordination_obligation_root",
            "fee_allocation_occurrence_root",
            "spend_intent_root",
            "safety_limit_binding_root",
            "selected_pool_id",
            "quote_asset_id",
            "zdex_asset_id",
        ):
            value = object.__getattribute__(self, name)
            if type(value) is not str:
                raise TypeError(f"Tokenomics V2 journal {name} must be exact str")
            _require_root(value, name=f"Tokenomics V2 journal {name}")
        _require_nonnegative_int(self.current_height, name="Tokenomics V2 journal height")
        for name in (
            "fee_charged_atoms",
            "buyback_allocation_atoms",
            "other_allocations_atoms",
            "carried_residue_atoms",
            "buyback_reserve_pre_atoms",
            "buyback_reserve_post_atoms",
            "quote_spend_atoms",
            "route_safe_quote_limit_atoms",
            "purchased_zdex_atoms",
            "burned_zdex_atoms",
            "live_supply_pre_atoms",
            "live_supply_post_atoms",
            "retained_supply_atoms",
            "remaining_epoch_burn_cap_pre_atoms",
            "remaining_epoch_burn_cap_post_atoms",
        ):
            _require_atoms_u128(
                object.__getattribute__(self, name),
                name=f"Tokenomics V2 journal {name}",
            )
        if not (self._spend_projection_holds() and self._burn_projection_holds()):
            raise ValueError("Tokenomics V2 journal accounting projection is inconsistent")

    def _spend_projection_holds(self) -> bool:
        return (
            0 < self.quote_spend_atoms <= self.route_safe_quote_limit_atoms
            and self.fee_charged_atoms
            == self.buyback_allocation_atoms
            + self.other_allocations_atoms
            + self.carried_residue_atoms
            and self.buyback_reserve_post_atoms + self.quote_spend_atoms
            == self.buyback_reserve_pre_atoms + self.buyback_allocation_atoms
            and self.pre_state_root != self.spend_post_state_root
        )

    def _burn_projection_holds(self) -> bool:
        return (
            self.burned_zdex_atoms != 0
            and self.purchased_zdex_atoms == self.burned_zdex_atoms
            and self.live_supply_post_atoms + self.burned_zdex_atoms
            == self.live_supply_pre_atoms
            and 0 < self.retained_supply_atoms <= self.live_supply_post_atoms
            and self.remaining_epoch_burn_cap_post_atoms
            + self.burned_zdex_atoms
            == self.remaining_epoch_burn_cap_pre_atoms
            and self.spend_post_state_root != self.post_state_root
        )

    @property
    def journal_root(self) -> str:
        self.validate()
        return hash_global_v1(
            "zdex-tokenomics-buyback-transition-journal-v2",
            self.to_canonical(),
        )

    def to_canonical(self) -> dict[str, object]:
        self.validate()
        return {
            "schema": ZDEX_TOKENOMICS_TRANSITION_JOURNAL_SCHEMA_V2,
            "context_root": self.context_root,
            "pre_state_root": self.pre_state_root,
            "spend_post_state_root": self.spend_post_state_root,
            "post_state_root": self.post_state_root,
            "spend_effect_plan_root": self.spend_effect_plan_root,
            "effect_plan_root": self.effect_plan_root,
            "quote_port_root": self.quote_port_root,
            "private_ports_root": self.private_ports_root,
            "discharged_obligation_id": self.discharged_obligation_id,
            "spot_context_root": self.spot_context_root,
            "spot_coordinates_root": self.spot_coordinates_root,
            "spot_post_state_root": self.spot_post_state_root,
            "lane_coordination_obligation_root": (
                self.lane_coordination_obligation_root
            ),
            "fee_allocation_occurrence_root": self.fee_allocation_occurrence_root,
            "spend_intent_root": self.spend_intent_root,
            "safety_limit_binding_root": self.safety_limit_binding_root,
            "selected_pool_id": self.selected_pool_id,
            "quote_asset_id": self.quote_asset_id,
            "zdex_asset_id": self.zdex_asset_id,
            "current_height": self.current_height,
            "fee_charged_atoms": self.fee_charged_atoms,
            "buyback_allocation_atoms": self.buyback_allocation_atoms,
            "other_allocations_atoms": self.other_allocations_atoms,
            "carried_residue_atoms": self.carried_residue_atoms,
            "buyback_reserve_pre_atoms": self.buyback_reserve_pre_atoms,
            "buyback_reserve_post_atoms": self.buyback_reserve_post_atoms,
            "quote_spend_atoms": self.quote_spend_atoms,
            "route_safe_quote_limit_atoms": self.route_safe_quote_limit_atoms,
            "purchased_zdex_atoms": self.purchased_zdex_atoms,
            "burned_zdex_atoms": self.burned_zdex_atoms,
            "live_supply_pre_atoms": self.live_supply_pre_atoms,
            "live_supply_post_atoms": self.live_supply_post_atoms,
            "retained_supply_atoms": self.retained_supply_atoms,
            "remaining_epoch_burn_cap_pre_atoms": (
                self.remaining_epoch_burn_cap_pre_atoms
            ),
            "remaining_epoch_burn_cap_post_atoms": (
                self.remaining_epoch_burn_cap_post_atoms
            ),
        }


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsBuybackRejectedV2:
    code: tokenomics_v1.ZDEXTokenomicsBuybackRejectCodeV1
    spend_code: ZDEXBuybackSpendRejectCodeV1 | None
    fee_code: ZDEXFeeAllocationRejectCodeV1 | None
    burn_code: tokenomics_v1.ZDEXTokenomicsBurnRejectCodeV1 | None
    pre_state: tokenomics_v1.ZDEXTokenomicsBuybackLaneStateV1
    post_state: tokenomics_v1.ZDEXTokenomicsBuybackLaneStateV1
    effects: GlobalEconomicEffectPlanV1 = field(
        default_factory=GlobalEconomicEffectPlanV1.empty
    )
    ports: None = None
    journal: None = None

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        if type(self.code) is not tokenomics_v1.ZDEXTokenomicsBuybackRejectCodeV1:
            raise TypeError("Tokenomics V2 reject code is not closed")
        spend_phase = self.code is tokenomics_v1.ZDEXTokenomicsBuybackRejectCodeV1.SPEND_REJECTED
        burn_phase = self.code is tokenomics_v1.ZDEXTokenomicsBuybackRejectCodeV1.BURN_REJECTED
        fee_phase = self.spend_code is ZDEXBuybackSpendRejectCodeV1.FEE_ALLOCATION_REJECTED
        if (
            spend_phase != (type(self.spend_code) is ZDEXBuybackSpendRejectCodeV1)
            or fee_phase != (type(self.fee_code) is ZDEXFeeAllocationRejectCodeV1)
            or burn_phase
            != (type(self.burn_code) is tokenomics_v1.ZDEXTokenomicsBurnRejectCodeV1)
        ):
            raise ValueError("Tokenomics V2 rejection phase codes are inconsistent")
        if type(self.pre_state) is not tokenomics_v1.ZDEXTokenomicsBuybackLaneStateV1:
            raise TypeError("Tokenomics V2 rejection pre-state is not closed")
        if type(self.post_state) is not tokenomics_v1.ZDEXTokenomicsBuybackLaneStateV1:
            raise TypeError("Tokenomics V2 rejection post-state is not closed")
        tokenomics_v1._require_revalidated_graph_v1(self.pre_state)
        if type(self.effects) is not GlobalEconomicEffectPlanV1:
            raise TypeError("Tokenomics V2 rejection effects are not closed")
        self.effects.validate()
        if self.pre_state is not self.post_state or not self.effects.is_empty:
            raise ValueError("Tokenomics V2 rejection must be an exact no-effect no-op")
        if self.ports is not None or self.journal is not None:
            raise ValueError("Tokenomics V2 rejection must expose no accepted projection")


@dataclass(frozen=True, slots=True)
class _ZDEXTokenomicsBuybackAcceptedFieldsV2:
    intent: tokenomics_v1._ZDEXTokenomicsIntentFieldsV1
    post_state: tokenomics_v1.ZDEXTokenomicsBuybackLaneStateV1
    effects: GlobalEconomicEffectPlanV1
    ports: ZDEXTokenomicsPrivatePortsV2
    journal: ZDEXTokenomicsBuybackJournalV2

    def validate(self) -> None:
        for value in (self.intent, self.post_state, self.effects):
            tokenomics_v1._require_exact_accepted_graph_v1(value)
        if type(self.ports) is not ZDEXTokenomicsPrivatePortsV2:
            raise TypeError("Tokenomics V2 accepted ports are not closed")
        if type(self.journal) is not ZDEXTokenomicsBuybackJournalV2:
            raise TypeError("Tokenomics V2 accepted journal is not closed")
        self.ports.validate()
        self.journal.validate()
        terminal = self.ports.burn_input
        if (
            self.journal.pre_state_root != self.intent.pre_state.state_root
            or self.journal.spend_post_state_root
            != self.intent.spend_post_state.state_root
            or self.journal.post_state_root != self.post_state.state_root
            or self.journal.spend_effect_plan_root
            != self.intent.spend_effects.effect_plan_root
            or self.journal.effect_plan_root != self.effects.effect_plan_root
            or self.journal.quote_port_root != self.ports.quote_output.port_root
            or self.journal.private_ports_root != self.ports.ports_root
            or self.journal.discharged_obligation_id != terminal.obligation_id
            or self.journal.spot_context_root != terminal.context.context_root
            or self.journal.spot_coordinates_root
            != terminal.context.coordinates.coordinates_root
            or self.journal.spot_post_state_root != terminal.post_state_root
            or self.journal.lane_coordination_obligation_root
            != zdex_tokenomics_complete_lane_obligation_root_v1()
        ):
            raise ValueError("Tokenomics V2 accepted projections disagree")


def _reject_v2(
    code: tokenomics_v1.ZDEXTokenomicsBuybackRejectCodeV1,
    state: tokenomics_v1.ZDEXTokenomicsBuybackLaneStateV1,
    *,
    spend_code: ZDEXBuybackSpendRejectCodeV1 | None = None,
    fee_code: ZDEXFeeAllocationRejectCodeV1 | None = None,
    burn_code: tokenomics_v1.ZDEXTokenomicsBurnRejectCodeV1 | None = None,
) -> ZDEXTokenomicsBuybackRejectedV2:
    return ZDEXTokenomicsBuybackRejectedV2(
        code,
        spend_code,
        fee_code,
        burn_code,
        state,
        state,
    )


def _map_v1_rejection_v2(
    rejected: tokenomics_v1.ZDEXTokenomicsBuybackRejectedV1,
) -> ZDEXTokenomicsBuybackRejectedV2:
    rejected.validate()
    return _reject_v2(
        rejected.code,
        rejected.pre_state,
        spend_code=rejected.spend_code,
        fee_code=rejected.fee_code,
        burn_code=rejected.burn_code,
    )


def _spot_flow_id_v2(
    role: ZDEXSpotFlowRoleV1,
    obligation: ZDEXSpotTerminalObligationV2,
    asset: str,
    source_principal: str,
    destination_principal: str,
    amount_atoms: int,
) -> str:
    return ZDEXSpotFlowIdentityV2(
        role,
        obligation.context,
        obligation.selected_pool_id,
        asset,
        source_principal,
        destination_principal,
        amount_atoms,
    ).flow_id


def _purchase_port_reject_v2(
    obligation: object,
    authority: tokenomics_v1.ZDEXTokenomicsBuybackAuthorityContextV1,
    intent: tokenomics_v1._ZDEXTokenomicsIntentFieldsV1,
    safe_limit_port: tokenomics_v1.ZDEXTokenomicsSafeLimitPortV1,
) -> tokenomics_v1.ZDEXTokenomicsBuybackRejectCodeV1 | None:
    if type(obligation) is not ZDEXSpotTerminalObligationV2:
        return tokenomics_v1.ZDEXTokenomicsBuybackRejectCodeV1.PURCHASE_PORT_MISMATCH
    try:
        obligation.validate()
    except (TypeError, ValueError):
        return tokenomics_v1.ZDEXTokenomicsBuybackRejectCodeV1.PURCHASE_PORT_MISMATCH
    quote = intent.quote_output
    policy = authority.execution_policy
    burn_principal = zdex_occurrence_burn_port_v1(
        profile_root=authority.profile_root,
        route_release_id=authority.route_release_id,
        command_occurrence_id=authority.command_occurrence_id,
    )
    zdex_pool = zdex_pool_reserve_principal_v1(
        pool_id=policy.pool_id,
        asset_id=policy.zdex_asset_id,
    )
    if (
        not _shared_occurrence_matches_v2(
            obligation.context,
            authority,
            quote,
            safe_limit_port.oracle_occurrence_id,
        )
        or obligation.consumer_module_release_id
        != authority.tokenomics_module_release_id
        or obligation.burn_asset != policy.zdex_asset_id
        or obligation.burn_principal != burn_principal
        or obligation.selected_pool_id != policy.pool_id
        or obligation.purchased_output_flow_id
        != _spot_flow_id_v2(
            ZDEXSpotFlowRoleV1.PURCHASED_ZDEX_OUTPUT,
            obligation,
            policy.zdex_asset_id,
            zdex_pool,
            burn_principal,
            obligation.purchased_atoms,
        )
    ):
        return tokenomics_v1.ZDEXTokenomicsBuybackRejectCodeV1.PURCHASE_PORT_MISMATCH
    if obligation.quote_input_flow_id != _spot_flow_id_v2(
        ZDEXSpotFlowRoleV1.QUOTE_INPUT,
        obligation,
        policy.quote_asset_id,
        quote.source_principal,
        quote.destination_principal,
        quote.amount_atoms,
    ):
        return tokenomics_v1.ZDEXTokenomicsBuybackRejectCodeV1.QUOTE_FLOW_MISMATCH
    return None


def _build_journal_v2(
    intent: tokenomics_v1._ZDEXTokenomicsIntentFieldsV1,
    port: tokenomics_v1.ZDEXTokenomicsSafeLimitPortV1,
    post_state: tokenomics_v1.ZDEXTokenomicsBuybackLaneStateV1,
    effects: GlobalEconomicEffectPlanV1,
    ports: ZDEXTokenomicsPrivatePortsV2,
    zdex_asset_id: str,
    amounts: tokenomics_v1._ZDEXTokenomicsBurnAmountsV1,
) -> ZDEXTokenomicsBuybackJournalV2:
    occurrence = intent.spend.fee_allocation.occurrence
    spend_intent = intent.spend.intent
    quote = intent.quote_output
    terminal = ports.burn_input
    return ZDEXTokenomicsBuybackJournalV2(
        context_root=intent.context_root,
        pre_state_root=quote.producer_quote_pre_state_root,
        spend_post_state_root=quote.producer_quote_post_state_root,
        post_state_root=post_state.state_root,
        spend_effect_plan_root=quote.producer_quote_effect_plan_root,
        effect_plan_root=effects.effect_plan_root,
        quote_port_root=quote.port_root,
        private_ports_root=ports.ports_root,
        discharged_obligation_id=terminal.obligation_id,
        spot_context_root=terminal.context.context_root,
        spot_coordinates_root=terminal.context.coordinates.coordinates_root,
        spot_post_state_root=terminal.post_state_root,
        lane_coordination_obligation_root=(
            zdex_tokenomics_complete_lane_obligation_root_v1()
        ),
        fee_allocation_occurrence_root=occurrence.occurrence_root,
        spend_intent_root=spend_intent.intent_root,
        safety_limit_binding_root=port.binding_root,
        selected_pool_id=quote.selected_pool_id,
        quote_asset_id=quote.quote_asset_id,
        zdex_asset_id=zdex_asset_id,
        current_height=port.current_height,
        fee_charged_atoms=occurrence.fee_charged_atoms,
        buyback_allocation_atoms=occurrence.buyback_quote_atoms,
        other_allocations_atoms=sum(
            row.allocation_atoms for row in occurrence.allocations[1:]
        ),
        carried_residue_atoms=occurrence.carried_residue_atoms,
        buyback_reserve_pre_atoms=spend_intent.buyback_reserve_before_atoms,
        buyback_reserve_post_atoms=(
            intent.spend.fee_post_state.destination_balances[0].allocation_atoms
        ),
        quote_spend_atoms=quote.amount_atoms,
        route_safe_quote_limit_atoms=port.route_safe_quote_limit_atoms,
        purchased_zdex_atoms=terminal.purchased_atoms,
        burned_zdex_atoms=amounts.purchased,
        live_supply_pre_atoms=amounts.live_pre,
        live_supply_post_atoms=amounts.live_post,
        retained_supply_atoms=amounts.retained,
        remaining_epoch_burn_cap_pre_atoms=amounts.cap_pre,
        remaining_epoch_burn_cap_post_atoms=amounts.cap_post,
    )


def _derive_transition_v2(
    candidate: ZDEXTokenomicsBuybackInputV2,
) -> _ZDEXTokenomicsBuybackAcceptedFieldsV2 | ZDEXTokenomicsBuybackRejectedV2:
    if type(candidate) is not ZDEXTokenomicsBuybackInputV2:
        raise TypeError("Tokenomics V2 candidate must be exact typed data")
    intent = tokenomics_v1._derive_intent_v1(candidate.intent_input)
    if type(intent) is tokenomics_v1.ZDEXTokenomicsBuybackRejectedV1:
        return _map_v1_rejection_v2(intent)
    if type(intent) is not tokenomics_v1._ZDEXTokenomicsIntentFieldsV1:
        raise TypeError("Tokenomics V2 intent result is not closed")
    authority = object.__getattribute__(candidate.intent_input, "authority")
    if type(authority) is not tokenomics_v1.ZDEXTokenomicsBuybackAuthorityContextV1:
        return _reject_v2(
            tokenomics_v1.ZDEXTokenomicsBuybackRejectCodeV1.AUTHORITY_MALFORMED,
            intent.pre_state,
        )
    port_reject = _purchase_port_reject_v2(
        candidate.spot_obligation,
        authority,
        intent,
        candidate.intent_input.safe_limit_port,
    )
    if port_reject is not None:
        return _reject_v2(port_reject, intent.pre_state)
    obligation = candidate.spot_obligation
    if type(obligation) is not ZDEXSpotTerminalObligationV2:
        raise TypeError("Tokenomics V2 admitted obligation is not closed")
    amounts = tokenomics_v1._derive_burn_amounts_v1(
        intent.pre_state.supply,
        authority.hyperdeflation_policy,
        obligation.purchased_atoms,
    )
    if type(amounts) is tokenomics_v1.ZDEXTokenomicsBurnRejectCodeV1:
        return _reject_v2(
            tokenomics_v1.ZDEXTokenomicsBuybackRejectCodeV1.BURN_REJECTED,
            intent.pre_state,
            burn_code=amounts,
        )
    if type(amounts) is not tokenomics_v1._ZDEXTokenomicsBurnAmountsV1:
        raise TypeError("Tokenomics V2 burn result is not closed")
    post_supply = replace(
        intent.pre_state.supply,
        live_supply_atoms=amounts.live_post,
        remaining_epoch_burn_cap_atoms=amounts.cap_post,
    )
    post_state = replace(intent.spend_post_state, supply=post_supply)
    effects = tokenomics_v1._build_effects_v1(
        intent,
        post_state,
        authority.execution_policy.zdex_asset_id,
        amounts,
    )
    ports = ZDEXTokenomicsPrivatePortsV2(intent.quote_output, obligation)
    journal = _build_journal_v2(
        intent,
        candidate.intent_input.safe_limit_port,
        post_state,
        effects,
        ports,
        authority.execution_policy.zdex_asset_id,
        amounts,
    )
    return _ZDEXTokenomicsBuybackAcceptedFieldsV2(
        intent,
        post_state,
        effects,
        ports,
        journal,
    )


def _accepted_fields_match_v2(
    expected: _ZDEXTokenomicsBuybackAcceptedFieldsV2,
    supplied: _ZDEXTokenomicsBuybackAcceptedFieldsV2,
) -> bool:
    expected.validate()
    supplied.validate()
    return (
        tokenomics_v1._exact_accepted_graph_matches_v1(
            expected.intent, supplied.intent
        )
        and tokenomics_v1._exact_accepted_graph_matches_v1(
            expected.post_state, supplied.post_state
        )
        and tokenomics_v1._exact_accepted_graph_matches_v1(
            expected.effects, supplied.effects
        )
        and expected.ports.to_canonical() == supplied.ports.to_canonical()
        and expected.journal.to_canonical() == supplied.journal.to_canonical()
    )


def _require_accepted_projection_v2(
    subject: object,
    fields: object,
    *,
    stale: bool,
) -> None:
    if type(subject) is not ZDEXTokenomicsBuybackInputV2:
        raise TypeError("Tokenomics V2 accepted subject is not closed")
    if type(fields) is not _ZDEXTokenomicsBuybackAcceptedFieldsV2:
        raise TypeError("Tokenomics V2 accepted fields are not closed")
    subject.__post_init__()
    fields.validate()
    expected = _derive_transition_v2(subject)
    if type(expected) is not _ZDEXTokenomicsBuybackAcceptedFieldsV2 or not (
        _accepted_fields_match_v2(expected, fields)
    ):
        suffix = "no longer rederives" if stale else "does not rederive"
        raise ValueError(f"Tokenomics V2 accepted projection {suffix}")


class ZDEXTokenomicsBuybackAcceptedV2:
    """Locally rederived SHADOW result without publication authority."""

    _subject: ZDEXTokenomicsBuybackInputV2
    _fields: _ZDEXTokenomicsBuybackAcceptedFieldsV2
    __slots__ = ("_subject", "_fields")

    def __init__(
        self,
        token: object,
        subject: ZDEXTokenomicsBuybackInputV2,
        fields: _ZDEXTokenomicsBuybackAcceptedFieldsV2,
    ) -> None:
        if token is not _ACCEPTED_TOKEN_V2:
            raise TypeError("Tokenomics V2 accepted result requires local rederivation")
        _require_accepted_projection_v2(subject, fields, stale=False)
        object.__setattr__(self, "_subject", subject)
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("Tokenomics V2 accepted result is immutable")

    @property
    def pre_state(self) -> tokenomics_v1.ZDEXTokenomicsBuybackLaneStateV1:
        return self._fields.intent.pre_state

    @property
    def spend_post_state(self) -> tokenomics_v1.ZDEXTokenomicsBuybackLaneStateV1:
        return self._fields.intent.spend_post_state

    @property
    def post_state(self) -> tokenomics_v1.ZDEXTokenomicsBuybackLaneStateV1:
        return self._fields.post_state

    @property
    def effects(self) -> GlobalEconomicEffectPlanV1:
        return self._fields.effects

    @property
    def quote_output(self) -> ZDEXAtomicBuybackQuotePortV2:
        return self._fields.intent.quote_output

    @property
    def ports(self) -> ZDEXTokenomicsPrivatePortsV2:
        return self._fields.ports

    @property
    def discharged_obligation(self) -> ZDEXSpotTerminalObligationV2:
        return self._fields.ports.burn_input

    @property
    def journal(self) -> ZDEXTokenomicsBuybackJournalV2:
        return self._fields.journal

    def validate(self) -> None:
        _require_accepted_projection_v2(
            object.__getattribute__(self, "_subject"),
            object.__getattribute__(self, "_fields"),
            stale=True,
        )


ZDEXTokenomicsBuybackResultV2: TypeAlias = (
    ZDEXTokenomicsBuybackAcceptedV2 | ZDEXTokenomicsBuybackRejectedV2
)


def transition_zdex_tokenomics_buyback_v2(
    candidate: ZDEXTokenomicsBuybackInputV2,
) -> ZDEXTokenomicsBuybackResultV2:
    """Rederive Phase A, discharge one V2 terminal, and propose exact burn effects."""

    derived = _derive_transition_v2(candidate)
    if type(derived) is ZDEXTokenomicsBuybackRejectedV2:
        return derived
    if type(derived) is not _ZDEXTokenomicsBuybackAcceptedFieldsV2:
        raise TypeError("Tokenomics V2 derivation result is not closed")
    return ZDEXTokenomicsBuybackAcceptedV2(_ACCEPTED_TOKEN_V2, candidate, derived)


__all__ = [
    "ZDEX_TOKENOMICS_PRIVATE_PORTS_SCHEMA_V2",
    "ZDEX_TOKENOMICS_TRANSITION_JOURNAL_SCHEMA_V2",
    "ZDEXTokenomicsBuybackAcceptedV2",
    "ZDEXTokenomicsBuybackInputV2",
    "ZDEXTokenomicsBuybackJournalV2",
    "ZDEXTokenomicsBuybackRejectedV2",
    "ZDEXTokenomicsBuybackResultV2",
    "ZDEXTokenomicsPrivatePortsV2",
    "transition_zdex_tokenomics_buyback_v2",
]
