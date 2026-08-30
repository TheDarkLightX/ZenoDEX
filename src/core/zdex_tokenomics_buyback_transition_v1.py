"""Bounded Tokenomics-lane transition for one governed ZDEX buy-and-burn.

The pure transition owns fee allocation, buyback-reserve spend, cadence,
the governed Spot quote output, exact purchased-ZDEX burn, and live-supply
update inside one complete tokenomics state.  Phase A derives the quote
output from committed fee ingress and the canonical reserve.  Phase B
re-derives phase A, binds the Spot terminal obligation to that exact quote,
and burns exactly the purchased amount under the retained-supply rule.

The tokenomics state carries no Spot pool reserve mirror: pool reserves stay
Spot-owned and purchased ZDEX awaiting burn is an ephemeral typed port.  The
quote output is the acyclic semantic port ``ZDEXAtomicBuybackQuotePortV2``:
it carries proof-independent producer/consumer release ids, producer pre/post
lane roots, the producer effect-plan root, the amount, and route, profile, and
occurrence coordinates.  It omits journal and receipt-binding roots, so no
hash fixed point can arise between the port, the module journal, and a
verified leaf wrapper.  The journal commits ``H(port)`` and the discharged
Spot obligation id for an outer route composer to pair; the leaf itself
claims no authenticated receipt binding.

This module is SHADOW research evidence.  It verifies no receipt, composes
no route, publishes no state, and grants no value-moving authority.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from dataclasses import fields as dataclass_fields
from enum import Enum
from typing import Final, TypeAlias, cast

from .global_settlement_types_v1 import (
    MAX_DELTA_ATOMS_V1,
    AssetConservationRowV1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    ExternalOutboxEnqueueV1,
    FeeConservationRowV1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    LaneWriteV1,
    _require_atoms_u128,
    _require_nonnegative_int,
    _require_root,
    _require_token,
    hash_global_v1,
)
from .zdex_atomic_buyback_quote_port_v2 import ZDEXAtomicBuybackQuotePortV2
from .zdex_buyback_spend_v1 import (
    ZDEXBuybackSpendAcceptedV1,
    ZDEXBuybackSpendContextV1,
    ZDEXBuybackSpendIntentV1,
    ZDEXBuybackSpendPolicyV1,
    ZDEXBuybackSpendRejectCodeV1,
    ZDEXBuybackSpendRejectedV1,
    ZDEXBuybackSpendStateV1,
    transition_zdex_buyback_spend_v1,
)
from .zdex_fee_allocation_types_v1 import (
    FEE_BUYBACK_PRINCIPAL_V1,
    ZDEXFeeAllocationAcceptedV1,
    ZDEXFeeAllocationCommandV1,
    ZDEXFeeAllocationContextV1,
    ZDEXFeeAllocationOccurrenceV1,
    ZDEXFeeAllocationPolicyV1,
    ZDEXFeeAllocationRejectCodeV1,
    ZDEXFeeDestinationAmountV1,
    ZDEXFeeDestinationV1,
    ZDEXFeeShareV1,
    ZDEXFeeStateV1,
)
from .zdex_hyperdeflation_math_v1 import retained_supply_atoms_v1
from .zdex_hyperdeflation_types_v1 import ZDEXHyperdeflationPolicyV1
from .zdex_purchase_burn_route_types_v1 import (
    PROTOCOL_BUYBACK_CUSTODY_DOMAIN_V1,
    PROTOCOL_SUPPLY_CUSTODY_DOMAIN_V1,
    ZDEX_SUPPLY_PRINCIPAL_V1,
    ZDEXBuybackExecutionPolicyV1,
    zdex_occurrence_burn_port_v1,
    zdex_pool_reserve_principal_v1,
)
from .zdex_spot_buyback_transition_v1 import (
    ZDEXSpotFlowIdentityV1,
    ZDEXSpotFlowRoleV1,
    ZDEXSpotTerminalObligationV1,
)
from .zdex_tokenomics_lane_v1 import MAX_ZDEX_TOKENOMICS_FEE_ASSETS_V1

ZDEX_TOKENOMICS_BUYBACK_RELEASE_SCHEMA_V1: Final = (
    "zenodex/zdex-tokenomics-buyback-release/v1"
)
ZDEX_TOKENOMICS_SUPPLY_CONTROL_SCHEMA_V1: Final = (
    "zenodex/zdex-tokenomics-supply-control/v1"
)
ZDEX_TOKENOMICS_BUYBACK_LANE_STATE_SCHEMA_V1: Final = (
    "zenodex/zdex-tokenomics-buyback-lane-state/v1"
)
ZDEX_TOKENOMICS_PROFILE_AUTHORIZATION_SCHEMA_V1: Final = (
    "zenodex/zdex-tokenomics-buyback-profile-authorization/v1"
)
ZDEX_TOKENOMICS_SAFE_LIMIT_PORT_SCHEMA_V1: Final = (
    "zenodex/zdex-tokenomics-safe-limit-port/v1"
)
ZDEX_TOKENOMICS_PRIVATE_PORTS_SCHEMA_V1: Final = (
    "zenodex/zdex-tokenomics-private-ports/v1"
)
ZDEX_TOKENOMICS_TRANSITION_JOURNAL_SCHEMA_V1: Final = (
    "zenodex/zdex-tokenomics-buyback-transition-journal/v1"
)
ZDEX_TOKENOMICS_FEE_ASSET_COUNT_CAP_V1: Final = MAX_ZDEX_TOKENOMICS_FEE_ASSETS_V1
_ACCEPTED_TOKEN_V1 = object()
_ACCEPTED_GRAPH_NODE_CAP_V1: Final = 4_096
_ACCEPTED_GRAPH_DEPTH_CAP_V1: Final = 64


class ZDEXTokenomicsBurnRejectCodeV1(str, Enum):
    RETAINED_SUPPLY_FLOOR_REACHED = "RETAINED_SUPPLY_FLOOR_REACHED"
    EPOCH_BURN_CAP_REACHED = "EPOCH_BURN_CAP_REACHED"
    BURN_EXCEEDS_CAPACITY = "BURN_EXCEEDS_CAPACITY"


class ZDEXTokenomicsBuybackRejectCodeV1(str, Enum):
    AUTHORITY_MALFORMED = "AUTHORITY_MALFORMED"
    RELEASE_MISMATCH = "RELEASE_MISMATCH"
    PROFILE_MISMATCH = "PROFILE_MISMATCH"
    STATE_COMMITMENT_MISMATCH = "STATE_COMMITMENT_MISMATCH"
    SAFETY_LIMIT_MISMATCH = "SAFETY_LIMIT_MISMATCH"
    POLICY_MISMATCH = "POLICY_MISMATCH"
    LANE_MALFORMED = "LANE_MALFORMED"
    SELECTION_MISMATCH = "SELECTION_MISMATCH"
    SPEND_REJECTED = "SPEND_REJECTED"
    PURCHASE_PORT_MISMATCH = "PURCHASE_PORT_MISMATCH"
    QUOTE_FLOW_MISMATCH = "QUOTE_FLOW_MISMATCH"
    BURN_REJECTED = "BURN_REJECTED"


def _require_exact_types(pairs: tuple[tuple[object, type], ...], *, name: str) -> None:
    if any(type(value) is not kind for value, kind in pairs):
        raise TypeError(f"{name} requires exact typed values")


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsSupplyControlStateV1:
    """Tokenomics-owned live supply and burn controls; no custody buckets."""

    asset_id: str
    policy_root: str
    decimals: int
    precision_epoch: int
    live_supply_atoms: int
    burn_budget_epoch: int
    remaining_epoch_burn_cap_atoms: int

    def __post_init__(self) -> None:
        _require_exact_accepted_graph_v1(self)
        _require_root(self.asset_id, name="Tokenomics supply asset id")
        _require_root(self.policy_root, name="Tokenomics supply policy root")
        for name in ("decimals", "precision_epoch", "burn_budget_epoch"):
            _require_nonnegative_int(getattr(self, name), name=f"Tokenomics supply {name}")
        live = _require_atoms_u128(self.live_supply_atoms, name="Tokenomics live supply")
        _require_atoms_u128(
            self.remaining_epoch_burn_cap_atoms,
            name="Tokenomics remaining epoch burn cap",
        )
        if live == 0:
            raise ValueError("Tokenomics live supply must be positive")

    @property
    def state_root(self) -> str:
        return hash_global_v1("zdex-tokenomics-supply-control-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "schema": ZDEX_TOKENOMICS_SUPPLY_CONTROL_SCHEMA_V1,
            "asset_id": self.asset_id,
            "policy_root": self.policy_root,
            "decimals": self.decimals,
            "precision_epoch": self.precision_epoch,
            "live_supply_atoms": self.live_supply_atoms,
            "burn_budget_epoch": self.burn_budget_epoch,
            "remaining_epoch_burn_cap_atoms": self.remaining_epoch_burn_cap_atoms,
        }


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsBuybackLaneStateV1:
    """One complete tokenomics state: supply, fee states, cadence, components."""

    supply: ZDEXTokenomicsSupplyControlStateV1
    fee_allocation_states: tuple[ZDEXFeeStateV1, ...]
    buyback_cadence_states: tuple[ZDEXBuybackSpendStateV1, ...]
    staking_state_root: str
    host_claims_state_root: str
    treasury_claims_state_root: str
    proof_rewards_state_root: str
    cover_reserve_state_root: str
    lp_rebates_state_root: str

    def __post_init__(self) -> None:
        _require_exact_accepted_graph_v1(self)
        if type(self.supply) is not ZDEXTokenomicsSupplyControlStateV1:
            raise TypeError("Tokenomics lane supply must be exact typed data")
        if type(self.fee_allocation_states) is not tuple or any(
            type(state) is not ZDEXFeeStateV1 for state in self.fee_allocation_states
        ):
            raise TypeError("Tokenomics lane fee states must be an exact tuple")
        if type(self.buyback_cadence_states) is not tuple or any(
            type(state) is not ZDEXBuybackSpendStateV1 for state in self.buyback_cadence_states
        ):
            raise TypeError("Tokenomics lane cadence states must be an exact tuple")
        fee_assets = tuple(state.fee_asset_id for state in self.fee_allocation_states)
        cadence_assets = tuple(state.quote_asset_id for state in self.buyback_cadence_states)
        if not 1 <= len(fee_assets) <= MAX_ZDEX_TOKENOMICS_FEE_ASSETS_V1:
            raise ValueError("Tokenomics lane fee-state registry width is unsupported")
        if fee_assets != tuple(sorted(set(fee_assets))):
            raise ValueError("Tokenomics lane fee states must be uniquely asset-ordered")
        if cadence_assets != fee_assets:
            raise ValueError("Tokenomics lane cadence must cover every fee asset in order")
        if self.supply.asset_id in fee_assets:
            raise ValueError("Tokenomics supply asset cannot also be a fee asset")
        for name in (
            "staking_state_root",
            "host_claims_state_root",
            "treasury_claims_state_root",
            "proof_rewards_state_root",
            "cover_reserve_state_root",
            "lp_rebates_state_root",
        ):
            _require_root(getattr(self, name), name=f"Tokenomics lane {name}")

    @property
    def state_root(self) -> str:
        return hash_global_v1("zdex-tokenomics-buyback-lane-state-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        _require_revalidated_graph_v1(self)
        return {
            "schema": ZDEX_TOKENOMICS_BUYBACK_LANE_STATE_SCHEMA_V1,
            "supply": self.supply,
            "fee_allocation_states": self.fee_allocation_states,
            "buyback_cadence_states": self.buyback_cadence_states,
            "staking_state_root": self.staking_state_root,
            "host_claims_state_root": self.host_claims_state_root,
            "treasury_claims_state_root": self.treasury_claims_state_root,
            "proof_rewards_state_root": self.proof_rewards_state_root,
            "cover_reserve_state_root": self.cover_reserve_state_root,
            "lp_rebates_state_root": self.lp_rebates_state_root,
        }


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsBuybackReleaseV1:
    tokenomics_module_release_id: str
    spot_module_release_id: str
    route_release_id: str
    fee_asset_count_cap: int

    def __post_init__(self) -> None:
        _require_exact_accepted_graph_v1(self)
        for name in (
            "tokenomics_module_release_id",
            "spot_module_release_id",
            "route_release_id",
        ):
            _require_root(getattr(self, name), name=f"Tokenomics release {name}")
        _require_nonnegative_int(self.fee_asset_count_cap, name="Tokenomics release fee cap")

    @property
    def release_root(self) -> str:
        return hash_global_v1("zdex-tokenomics-buyback-release-v1", self.to_canonical())

    @property
    def is_bounded_v1(self) -> bool:
        return self.fee_asset_count_cap == ZDEX_TOKENOMICS_FEE_ASSET_COUNT_CAP_V1

    def to_canonical(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "schema": ZDEX_TOKENOMICS_BUYBACK_RELEASE_SCHEMA_V1,
            "tokenomics_module_release_id": self.tokenomics_module_release_id,
            "spot_module_release_id": self.spot_module_release_id,
            "route_release_id": self.route_release_id,
            "fee_asset_count_cap": self.fee_asset_count_cap,
        }


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsProfileAuthorizationV1:
    profile_root: str
    chain_id: str
    deployment_root: str
    route_release_id: str
    spot_module_release_id: str
    tokenomics_module_release_id: str
    release_root: str
    execution_policy_root: str
    fee_policy_root: str
    spend_policy_root: str
    hyperdeflation_policy_root: str
    price_policy_root: str

    def __post_init__(self) -> None:
        _require_exact_accepted_graph_v1(self)
        _require_token(self.chain_id, name="Tokenomics profile chain id")
        for name in (
            "profile_root",
            "deployment_root",
            "route_release_id",
            "spot_module_release_id",
            "tokenomics_module_release_id",
            "release_root",
            "execution_policy_root",
            "fee_policy_root",
            "spend_policy_root",
            "hyperdeflation_policy_root",
            "price_policy_root",
        ):
            _require_root(getattr(self, name), name=f"Tokenomics profile {name}")

    @property
    def authorization_root(self) -> str:
        return hash_global_v1(
            "zdex-tokenomics-buyback-profile-authorization-v1",
            self.to_canonical(),
        )

    def to_canonical(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "schema": ZDEX_TOKENOMICS_PROFILE_AUTHORIZATION_SCHEMA_V1,
            "profile_root": self.profile_root,
            "chain_id": self.chain_id,
            "deployment_root": self.deployment_root,
            "route_release_id": self.route_release_id,
            "spot_module_release_id": self.spot_module_release_id,
            "tokenomics_module_release_id": self.tokenomics_module_release_id,
            "release_root": self.release_root,
            "execution_policy_root": self.execution_policy_root,
            "fee_policy_root": self.fee_policy_root,
            "spend_policy_root": self.spend_policy_root,
            "hyperdeflation_policy_root": self.hyperdeflation_policy_root,
            "price_policy_root": self.price_policy_root,
        }


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsBuybackAuthorityContextV1:
    chain_id: str
    deployment_root: str
    profile_root: str
    profile_authorization_root: str
    route_release_id: str
    command_occurrence_id: str
    global_pre_state_root: str
    tokenomics_pre_state_root: str
    writer_epoch: int
    current_height: int
    spot_module_release_id: str
    tokenomics_module_release_id: str
    price_policy_root: str
    release: ZDEXTokenomicsBuybackReleaseV1
    execution_policy: ZDEXBuybackExecutionPolicyV1
    fee_policy: ZDEXFeeAllocationPolicyV1
    spend_policy: ZDEXBuybackSpendPolicyV1
    hyperdeflation_policy: ZDEXHyperdeflationPolicyV1
    profile_authorization: ZDEXTokenomicsProfileAuthorizationV1

    def __post_init__(self) -> None:
        _require_exact_accepted_graph_v1(self)
        _require_token(self.chain_id, name="Tokenomics authority chain id")
        for name in (
            "deployment_root",
            "profile_root",
            "profile_authorization_root",
            "route_release_id",
            "command_occurrence_id",
            "global_pre_state_root",
            "tokenomics_pre_state_root",
            "spot_module_release_id",
            "tokenomics_module_release_id",
            "price_policy_root",
        ):
            _require_root(getattr(self, name), name=f"Tokenomics authority {name}")
        _require_nonnegative_int(self.writer_epoch, name="Tokenomics authority writer epoch")
        _require_nonnegative_int(self.current_height, name="Tokenomics authority current height")
        _require_exact_types(
            (
                (self.release, ZDEXTokenomicsBuybackReleaseV1),
                (self.execution_policy, ZDEXBuybackExecutionPolicyV1),
                (self.fee_policy, ZDEXFeeAllocationPolicyV1),
                (self.spend_policy, ZDEXBuybackSpendPolicyV1),
                (self.hyperdeflation_policy, ZDEXHyperdeflationPolicyV1),
                (self.profile_authorization, ZDEXTokenomicsProfileAuthorizationV1),
            ),
            name="Tokenomics authority nested values",
        )


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsSafeLimitPortV1:
    """Spot/Oracle route-safe quote limit as typed provenance for this leaf."""

    profile_root: str
    route_release_id: str
    command_occurrence_id: str
    global_pre_state_root: str
    tokenomics_pre_state_root: str
    selected_pool_id: str
    quote_asset_id: str
    zdex_asset_id: str
    price_policy_root: str
    oracle_occurrence_id: str
    binding_root: str
    current_height: int
    route_safe_quote_limit_atoms: int

    def __post_init__(self) -> None:
        _require_exact_accepted_graph_v1(self)
        for name in (
            "profile_root",
            "route_release_id",
            "command_occurrence_id",
            "global_pre_state_root",
            "tokenomics_pre_state_root",
            "selected_pool_id",
            "quote_asset_id",
            "zdex_asset_id",
            "price_policy_root",
            "oracle_occurrence_id",
            "binding_root",
        ):
            _require_root(getattr(self, name), name=f"Tokenomics safe limit {name}")
        _require_nonnegative_int(self.current_height, name="Tokenomics safe limit height")
        limit = _require_atoms_u128(
            self.route_safe_quote_limit_atoms,
            name="Tokenomics route safe quote limit",
        )
        if limit > MAX_DELTA_ATOMS_V1:
            raise ValueError("Tokenomics route safe quote limit must fit a signed effect")

    def to_canonical(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "schema": ZDEX_TOKENOMICS_SAFE_LIMIT_PORT_SCHEMA_V1,
            "profile_root": self.profile_root,
            "route_release_id": self.route_release_id,
            "command_occurrence_id": self.command_occurrence_id,
            "global_pre_state_root": self.global_pre_state_root,
            "tokenomics_pre_state_root": self.tokenomics_pre_state_root,
            "selected_pool_id": self.selected_pool_id,
            "quote_asset_id": self.quote_asset_id,
            "zdex_asset_id": self.zdex_asset_id,
            "price_policy_root": self.price_policy_root,
            "oracle_occurrence_id": self.oracle_occurrence_id,
            "binding_root": self.binding_root,
            "current_height": self.current_height,
            "route_safe_quote_limit_atoms": self.route_safe_quote_limit_atoms,
        }


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsBuybackIntentInputV1:
    authority: object
    pre_state: ZDEXTokenomicsBuybackLaneStateV1
    safe_limit_port: ZDEXTokenomicsSafeLimitPortV1

    def __post_init__(self) -> None:
        _require_exact_types(
            (
                (self.pre_state, ZDEXTokenomicsBuybackLaneStateV1),
                (self.safe_limit_port, ZDEXTokenomicsSafeLimitPortV1),
            ),
            name="Tokenomics intent input",
        )
        _require_revalidated_graph_v1(self.pre_state)
        _require_revalidated_graph_v1(self.safe_limit_port)


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsBuybackInputV1:
    intent_input: ZDEXTokenomicsBuybackIntentInputV1
    spot_obligation: object

    def __post_init__(self) -> None:
        if type(self.intent_input) is not ZDEXTokenomicsBuybackIntentInputV1:
            raise TypeError("Tokenomics buyback input requires an exact intent input")
        self.intent_input.__post_init__()


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsPrivatePortsV1:
    """The produced quote port and the consumed Spot obligation, as one pair."""

    quote_output: ZDEXAtomicBuybackQuotePortV2
    burn_input: ZDEXSpotTerminalObligationV1

    def __post_init__(self) -> None:
        _require_exact_accepted_graph_v1(self)
        _require_revalidated_graph_v1(self.quote_output)
        _require_revalidated_graph_v1(self.burn_input)
        _require_exact_types(
            (
                (self.quote_output, ZDEXAtomicBuybackQuotePortV2),
                (self.burn_input, ZDEXSpotTerminalObligationV1),
            ),
            name="Tokenomics private ports",
        )
        if (
            self.quote_output.selected_pool_id != self.burn_input.selected_pool_id
            or self.quote_output.producer_module_release_id
            != self.burn_input.consumer_module_release_id
        ):
            raise ValueError("Tokenomics private ports do not form one exact role pair")

    @property
    def ports_root(self) -> str:
        self.__post_init__()
        return hash_global_v1(
            "zdex-tokenomics-private-ports-v1",
            {
                "schema": ZDEX_TOKENOMICS_PRIVATE_PORTS_SCHEMA_V1,
                "quote_port_root": self.quote_output.port_root,
                "burn_input_obligation_id": self.burn_input.obligation_id,
                "quote_amount_atoms": self.quote_output.amount_atoms,
                "burn_amount_atoms": self.burn_input.purchased_atoms,
            },
        )


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsBuybackJournalV1:
    """Complete witness of the Lean accounting premises owned by this lane.

    ``F = b + other + r``, ``B1 + q = B0 + b``, ``purchased = burned``,
    ``live_post + p = live_pre``, and ``cap_post + p = cap_pre``.
    """

    context_root: str
    pre_state_root: str
    spend_post_state_root: str
    post_state_root: str
    spend_effect_plan_root: str
    effect_plan_root: str
    quote_port_root: str
    private_ports_root: str
    discharged_obligation_id: str
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
        _require_exact_accepted_graph_v1(self)
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
            "fee_allocation_occurrence_root",
            "spend_intent_root",
            "safety_limit_binding_root",
            "selected_pool_id",
            "quote_asset_id",
            "zdex_asset_id",
        ):
            _require_root(getattr(self, name), name=f"Tokenomics journal {name}")
        _require_nonnegative_int(self.current_height, name="Tokenomics journal height")
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
            _require_atoms_u128(getattr(self, name), name=f"Tokenomics journal {name}")
        if not (self._spend_projection_holds() and self._burn_projection_holds()):
            raise ValueError("Tokenomics journal accounting projection is inconsistent")

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
            and self.live_supply_post_atoms + self.burned_zdex_atoms == self.live_supply_pre_atoms
            and 0 < self.retained_supply_atoms <= self.live_supply_post_atoms
            and self.remaining_epoch_burn_cap_post_atoms + self.burned_zdex_atoms
            == self.remaining_epoch_burn_cap_pre_atoms
            and self.spend_post_state_root != self.post_state_root
        )

    @property
    def journal_root(self) -> str:
        return hash_global_v1(
            "zdex-tokenomics-buyback-transition-journal-v1",
            {"schema": ZDEX_TOKENOMICS_TRANSITION_JOURNAL_SCHEMA_V1, **self.to_canonical()},
        )

    def to_canonical(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "context_root": self.context_root,
            "pre_state_root": self.pre_state_root,
            "spend_post_state_root": self.spend_post_state_root,
            "post_state_root": self.post_state_root,
            "spend_effect_plan_root": self.spend_effect_plan_root,
            "effect_plan_root": self.effect_plan_root,
            "quote_port_root": self.quote_port_root,
            "private_ports_root": self.private_ports_root,
            "discharged_obligation_id": self.discharged_obligation_id,
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
            "remaining_epoch_burn_cap_pre_atoms": self.remaining_epoch_burn_cap_pre_atoms,
            "remaining_epoch_burn_cap_post_atoms": self.remaining_epoch_burn_cap_post_atoms,
        }


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsBuybackRejectedV1:
    code: ZDEXTokenomicsBuybackRejectCodeV1
    spend_code: ZDEXBuybackSpendRejectCodeV1 | None
    fee_code: ZDEXFeeAllocationRejectCodeV1 | None
    burn_code: ZDEXTokenomicsBurnRejectCodeV1 | None
    pre_state: ZDEXTokenomicsBuybackLaneStateV1
    post_state: ZDEXTokenomicsBuybackLaneStateV1
    effects: GlobalEconomicEffectPlanV1 = GlobalEconomicEffectPlanV1.empty()
    ports: None = None
    journal: None = None

    def __post_init__(self) -> None:
        _require_exact_accepted_graph_v1(self)
        if type(self.code) is not ZDEXTokenomicsBuybackRejectCodeV1:
            raise TypeError("Tokenomics buyback reject code is not closed")
        spend_phase = self.code is ZDEXTokenomicsBuybackRejectCodeV1.SPEND_REJECTED
        burn_phase = self.code is ZDEXTokenomicsBuybackRejectCodeV1.BURN_REJECTED
        fee_phase = self.spend_code is ZDEXBuybackSpendRejectCodeV1.FEE_ALLOCATION_REJECTED
        if (
            spend_phase != (type(self.spend_code) is ZDEXBuybackSpendRejectCodeV1)
            or fee_phase != (type(self.fee_code) is ZDEXFeeAllocationRejectCodeV1)
            or burn_phase != (type(self.burn_code) is ZDEXTokenomicsBurnRejectCodeV1)
        ):
            raise ValueError("Tokenomics buyback rejection phase codes are inconsistent")
        if self.pre_state is not self.post_state or not self.effects.is_empty:
            raise ValueError("Tokenomics buyback rejection must be an exact no-effect no-op")
        _require_revalidated_graph_v1(self.pre_state)

    def validate(self) -> None:
        self.__post_init__()


@dataclass(frozen=True, slots=True)
class _ZDEXTokenomicsIntentFieldsV1:
    pre_state: ZDEXTokenomicsBuybackLaneStateV1
    spend_post_state: ZDEXTokenomicsBuybackLaneStateV1
    spend_effects: GlobalEconomicEffectPlanV1
    spend: ZDEXBuybackSpendAcceptedV1
    quote_output: ZDEXAtomicBuybackQuotePortV2
    context_root: str


@dataclass(frozen=True, slots=True)
class _ZDEXTokenomicsBuybackAcceptedFieldsV1:
    intent: _ZDEXTokenomicsIntentFieldsV1
    post_state: ZDEXTokenomicsBuybackLaneStateV1
    effects: GlobalEconomicEffectPlanV1
    ports: ZDEXTokenomicsPrivatePortsV1
    journal: ZDEXTokenomicsBuybackJournalV1


_ACCEPTED_GRAPH_ENUM_TYPES_V1: Final = frozenset(
    {
        EconomicEffectKindV1,
        LaneIdV1,
        ZDEXBuybackSpendRejectCodeV1,
        ZDEXFeeAllocationRejectCodeV1,
        ZDEXFeeDestinationV1,
        ZDEXTokenomicsBurnRejectCodeV1,
        ZDEXTokenomicsBuybackRejectCodeV1,
    }
)

_ACCEPTED_GRAPH_LEAF_TYPES_V1: Final = frozenset(
    {str, int, bool, type(None)} | set(_ACCEPTED_GRAPH_ENUM_TYPES_V1)
)

_ACCEPTED_GRAPH_DATACLASS_TYPES_V1: Final = frozenset(
    {
        AssetConservationRowV1,
        EconomicEffectRowV1,
        ExternalOutboxEnqueueV1,
        FeeConservationRowV1,
        GlobalEconomicEffectPlanV1,
        LaneWriteV1,
        ZDEXFeeShareV1,
        ZDEXFeeAllocationPolicyV1,
        ZDEXFeeDestinationAmountV1,
        ZDEXFeeStateV1,
        ZDEXFeeAllocationContextV1,
        ZDEXFeeAllocationCommandV1,
        ZDEXFeeAllocationOccurrenceV1,
        ZDEXFeeAllocationAcceptedV1,
        ZDEXBuybackSpendPolicyV1,
        ZDEXBuybackSpendStateV1,
        ZDEXBuybackSpendContextV1,
        ZDEXBuybackSpendIntentV1,
        ZDEXBuybackSpendAcceptedV1,
        ZDEXHyperdeflationPolicyV1,
        ZDEXBuybackExecutionPolicyV1,
        ZDEXSpotTerminalObligationV1,
        ZDEXTokenomicsSupplyControlStateV1,
        ZDEXTokenomicsBuybackLaneStateV1,
        ZDEXTokenomicsBuybackReleaseV1,
        ZDEXTokenomicsProfileAuthorizationV1,
        ZDEXTokenomicsBuybackAuthorityContextV1,
        ZDEXTokenomicsSafeLimitPortV1,
        ZDEXTokenomicsBuybackIntentInputV1,
        ZDEXTokenomicsBuybackInputV1,
        ZDEXAtomicBuybackQuotePortV2,
        ZDEXTokenomicsPrivatePortsV1,
        ZDEXTokenomicsBuybackJournalV1,
        ZDEXTokenomicsBuybackRejectedV1,
        _ZDEXTokenomicsIntentFieldsV1,
        _ZDEXTokenomicsBuybackAcceptedFieldsV1,
    }
)


def _require_exact_accepted_graph_v1(value: object) -> None:
    """Reject foreign behavior, cycles, and oversized graphs before comparison."""

    active_ids: set[int] = set()
    visited_nodes = 0

    def visit(node: object, depth: int) -> None:
        nonlocal visited_nodes
        visited_nodes += 1
        if visited_nodes > _ACCEPTED_GRAPH_NODE_CAP_V1:
            raise ValueError("Tokenomics buyback accepted graph exceeds node budget")
        if depth > _ACCEPTED_GRAPH_DEPTH_CAP_V1:
            raise ValueError("Tokenomics buyback accepted graph exceeds depth budget")
        node_type = type(node)
        if node_type in _ACCEPTED_GRAPH_LEAF_TYPES_V1:
            return
        node_id = id(node)
        if node_id in active_ids:
            raise ValueError("Tokenomics buyback accepted graph contains a cycle")
        active_ids.add(node_id)
        try:
            if node_type is tuple:
                for item in cast(tuple[object, ...], node):
                    visit(item, depth + 1)
                return
            if node_type not in _ACCEPTED_GRAPH_DATACLASS_TYPES_V1:
                raise TypeError("Tokenomics buyback accepted owned graph is not closed")
            dataclass_type = cast(type[_ZDEXTokenomicsBuybackAcceptedFieldsV1], node_type)
            for field in dataclass_fields(dataclass_type):
                visit(object.__getattribute__(node, field.name), depth + 1)
        finally:
            active_ids.remove(node_id)

    visit(value, 0)


def _require_revalidated_graph_v1(value: object) -> None:
    """Re-run every constructor invariant after proving the graph is inert.

    The exact-shape pass must run first.  It prevents a retained str/int
    subclass or foreign dataclass from executing behavior inside a nested
    ``__post_init__``, equality check, or canonical encoder.
    """

    _require_exact_accepted_graph_v1(value)
    validated_ids: set[int] = set()

    def visit(node: object) -> None:
        node_type = type(node)
        if node_type in _ACCEPTED_GRAPH_LEAF_TYPES_V1:
            return
        node_id = id(node)
        if node_id in validated_ids:
            return
        if node_type is tuple:
            for item in cast(tuple[object, ...], node):
                visit(item)
            validated_ids.add(node_id)
            return
        dataclass_type = cast(type[_ZDEXTokenomicsBuybackAcceptedFieldsV1], node_type)
        for field in dataclass_fields(dataclass_type):
            visit(object.__getattribute__(node, field.name))
        post_init = getattr(dataclass_type, "__post_init__", None)
        if post_init is not None:
            post_init(node)
        validated_ids.add(node_id)

    visit(value)


def _is_revalidated_graph_v1(value: object, expected_type: type[object]) -> bool:
    if type(value) is not expected_type:
        return False
    try:
        _require_revalidated_graph_v1(value)
    except (TypeError, ValueError):
        return False
    return True


def _exact_accepted_graph_matches_v1(expected: object, supplied: object) -> bool:
    """Compare closed graphs without Python's cross-type equality aliases."""

    if type(expected) is not type(supplied):
        return False
    value_type = type(expected)
    if value_type is type(None):
        return True
    if value_type in _ACCEPTED_GRAPH_ENUM_TYPES_V1:
        return expected is supplied
    if value_type in {str, int, bool}:
        return expected == supplied
    if value_type is tuple:
        expected_items = cast(tuple[object, ...], expected)
        supplied_items = cast(tuple[object, ...], supplied)
        return len(expected_items) == len(supplied_items) and all(
            _exact_accepted_graph_matches_v1(left, right)
            for left, right in zip(expected_items, supplied_items, strict=True)
        )
    if value_type not in _ACCEPTED_GRAPH_DATACLASS_TYPES_V1:
        return False
    dataclass_type = cast(type[_ZDEXTokenomicsBuybackAcceptedFieldsV1], value_type)
    return all(
        _exact_accepted_graph_matches_v1(
            object.__getattribute__(expected, field.name),
            object.__getattribute__(supplied, field.name),
        )
        for field in dataclass_fields(dataclass_type)
    )


class ZDEXTokenomicsBuybackIntentV1:
    """Revalidated phase-A result; data rather than publication authority."""

    _subject: ZDEXTokenomicsBuybackIntentInputV1
    _fields: _ZDEXTokenomicsIntentFieldsV1
    __slots__ = ("_subject", "_fields")

    def __init__(
        self,
        token: object,
        subject: ZDEXTokenomicsBuybackIntentInputV1,
        fields: _ZDEXTokenomicsIntentFieldsV1,
    ) -> None:
        if token is not _ACCEPTED_TOKEN_V1:
            raise TypeError("Tokenomics buyback intent requires local rederivation")
        _require_intent_projection_v1(subject, fields, stale=False)
        object.__setattr__(self, "_subject", subject)
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("Tokenomics buyback intent is immutable")

    @property
    def pre_state(self) -> ZDEXTokenomicsBuybackLaneStateV1:
        return self._fields.pre_state

    @property
    def spend_post_state(self) -> ZDEXTokenomicsBuybackLaneStateV1:
        return self._fields.spend_post_state

    @property
    def spend_effects(self) -> GlobalEconomicEffectPlanV1:
        return self._fields.spend_effects

    @property
    def spend(self) -> ZDEXBuybackSpendAcceptedV1:
        return self._fields.spend

    @property
    def quote_output(self) -> ZDEXAtomicBuybackQuotePortV2:
        return self._fields.quote_output

    @property
    def context_root(self) -> str:
        return self._fields.context_root

    def validate(self) -> None:
        _require_intent_projection_v1(
            object.__getattribute__(self, "_subject"),
            object.__getattribute__(self, "_fields"),
            stale=True,
        )


class ZDEXTokenomicsBuybackAcceptedV1:
    """Revalidated SHADOW result; it is data rather than publication authority."""

    _subject: ZDEXTokenomicsBuybackInputV1
    _fields: _ZDEXTokenomicsBuybackAcceptedFieldsV1
    __slots__ = ("_subject", "_fields")

    def __init__(
        self,
        token: object,
        subject: ZDEXTokenomicsBuybackInputV1,
        fields: _ZDEXTokenomicsBuybackAcceptedFieldsV1,
    ) -> None:
        if token is not _ACCEPTED_TOKEN_V1:
            raise TypeError("Tokenomics buyback accepted result requires local rederivation")
        _require_accepted_projection_v1(subject, fields, stale=False)
        object.__setattr__(self, "_subject", subject)
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("Tokenomics buyback accepted result is immutable")

    @property
    def pre_state(self) -> ZDEXTokenomicsBuybackLaneStateV1:
        return self._fields.intent.pre_state

    @property
    def spend_post_state(self) -> ZDEXTokenomicsBuybackLaneStateV1:
        return self._fields.intent.spend_post_state

    @property
    def post_state(self) -> ZDEXTokenomicsBuybackLaneStateV1:
        return self._fields.post_state

    @property
    def spend_effects(self) -> GlobalEconomicEffectPlanV1:
        return self._fields.intent.spend_effects

    @property
    def effects(self) -> GlobalEconomicEffectPlanV1:
        return self._fields.effects

    @property
    def spend(self) -> ZDEXBuybackSpendAcceptedV1:
        return self._fields.intent.spend

    @property
    def quote_output(self) -> ZDEXAtomicBuybackQuotePortV2:
        return self._fields.intent.quote_output

    @property
    def ports(self) -> ZDEXTokenomicsPrivatePortsV1:
        return self._fields.ports

    @property
    def journal(self) -> ZDEXTokenomicsBuybackJournalV1:
        return self._fields.journal

    @property
    def discharged_obligation(self) -> ZDEXSpotTerminalObligationV1:
        return self._fields.ports.burn_input

    def validate(self) -> None:
        _require_accepted_projection_v1(
            object.__getattribute__(self, "_subject"),
            object.__getattribute__(self, "_fields"),
            stale=True,
        )


ZDEXTokenomicsBuybackIntentResultV1: TypeAlias = (
    ZDEXTokenomicsBuybackIntentV1 | ZDEXTokenomicsBuybackRejectedV1
)
ZDEXTokenomicsBuybackResultV1: TypeAlias = (
    ZDEXTokenomicsBuybackAcceptedV1 | ZDEXTokenomicsBuybackRejectedV1
)


def _require_intent_projection_v1(subject: object, fields: object, *, stale: bool) -> None:
    if type(subject) is not ZDEXTokenomicsBuybackIntentInputV1:
        raise TypeError("Tokenomics buyback intent subject is not closed")
    if type(fields) is not _ZDEXTokenomicsIntentFieldsV1:
        raise TypeError("Tokenomics buyback intent fields are not closed")
    _require_exact_accepted_graph_v1(subject)
    _require_exact_accepted_graph_v1(fields)
    expected = _derive_intent_v1(subject)
    if type(expected) is not _ZDEXTokenomicsIntentFieldsV1 or not (
        _exact_accepted_graph_matches_v1(expected, fields)
    ):
        suffix = "no longer rederives" if stale else "does not rederive"
        raise ValueError(f"Tokenomics buyback intent projection {suffix}")


def _require_accepted_projection_v1(subject: object, fields: object, *, stale: bool) -> None:
    if type(subject) is not ZDEXTokenomicsBuybackInputV1:
        raise TypeError("Tokenomics buyback accepted subject is not closed")
    if type(fields) is not _ZDEXTokenomicsBuybackAcceptedFieldsV1:
        raise TypeError("Tokenomics buyback accepted fields are not closed")
    _require_exact_accepted_graph_v1(subject)
    _require_exact_accepted_graph_v1(fields)
    expected = _derive_transition_v1(subject)
    if type(expected) is not _ZDEXTokenomicsBuybackAcceptedFieldsV1 or not (
        _exact_accepted_graph_matches_v1(expected, fields)
    ):
        suffix = "no longer rederives" if stale else "does not rederive"
        raise ValueError(f"Tokenomics buyback accepted projection {suffix}")


@dataclass(frozen=True, slots=True)
class _ZDEXTokenomicsSelectionV1:
    fee_state: ZDEXFeeStateV1
    cadence: ZDEXBuybackSpendStateV1


@dataclass(frozen=True, slots=True)
class _ZDEXTokenomicsBurnAmountsV1:
    purchased: int
    retained: int
    live_pre: int
    live_post: int
    cap_pre: int
    cap_post: int


def _reject(
    code: ZDEXTokenomicsBuybackRejectCodeV1,
    state: ZDEXTokenomicsBuybackLaneStateV1,
    *,
    spend_code: ZDEXBuybackSpendRejectCodeV1 | None = None,
    fee_code: ZDEXFeeAllocationRejectCodeV1 | None = None,
    burn_code: ZDEXTokenomicsBurnRejectCodeV1 | None = None,
) -> ZDEXTokenomicsBuybackRejectedV1:
    return ZDEXTokenomicsBuybackRejectedV1(code, spend_code, fee_code, burn_code, state, state)


def _context_root_v1(
    authority: ZDEXTokenomicsBuybackAuthorityContextV1,
    port: ZDEXTokenomicsSafeLimitPortV1,
) -> str:
    return hash_global_v1(
        "zdex-tokenomics-buyback-transition-context-v1",
        {
            "chain_id": authority.chain_id,
            "deployment_root": authority.deployment_root,
            "profile_root": authority.profile_root,
            "profile_authorization_root": authority.profile_authorization_root,
            "route_release_id": authority.route_release_id,
            "command_occurrence_id": authority.command_occurrence_id,
            "global_pre_state_root": authority.global_pre_state_root,
            "tokenomics_pre_state_root": authority.tokenomics_pre_state_root,
            "writer_epoch": authority.writer_epoch,
            "current_height": authority.current_height,
            "spot_module_release_id": authority.spot_module_release_id,
            "tokenomics_module_release_id": authority.tokenomics_module_release_id,
            "release_root": authority.release.release_root,
            "execution_policy_root": authority.execution_policy.policy_root,
            "fee_policy_root": authority.fee_policy.policy_root,
            "spend_policy_root": authority.spend_policy.policy_root,
            "hyperdeflation_policy_root": authority.hyperdeflation_policy.policy_root,
            "price_policy_root": authority.price_policy_root,
            "oracle_occurrence_id": port.oracle_occurrence_id,
            "safety_limit_binding_root": port.binding_root,
            "route_safe_quote_limit_atoms": port.route_safe_quote_limit_atoms,
        },
    )


def _release_matches_v1(authority: ZDEXTokenomicsBuybackAuthorityContextV1) -> bool:
    release = authority.release
    return (
        release.is_bounded_v1
        and authority.route_release_id == release.route_release_id
        and authority.spot_module_release_id == release.spot_module_release_id
        and authority.tokenomics_module_release_id == release.tokenomics_module_release_id
    )


def _profile_matches_v1(authority: ZDEXTokenomicsBuybackAuthorityContextV1) -> bool:
    profile = authority.profile_authorization
    return (
        authority.profile_authorization_root == profile.authorization_root
        and profile.profile_root == authority.profile_root
        and profile.chain_id == authority.chain_id
        and profile.deployment_root == authority.deployment_root
        and profile.route_release_id == authority.route_release_id
        and profile.spot_module_release_id == authority.spot_module_release_id
        and profile.tokenomics_module_release_id == authority.tokenomics_module_release_id
        and profile.release_root == authority.release.release_root
        and profile.execution_policy_root == authority.execution_policy.policy_root
        and profile.fee_policy_root == authority.fee_policy.policy_root
        and profile.spend_policy_root == authority.spend_policy.policy_root
        and profile.hyperdeflation_policy_root == authority.hyperdeflation_policy.policy_root
        and profile.price_policy_root == authority.price_policy_root
    )


def _safe_limit_matches_v1(
    candidate: ZDEXTokenomicsBuybackIntentInputV1,
    authority: ZDEXTokenomicsBuybackAuthorityContextV1,
) -> bool:
    port = candidate.safe_limit_port
    if not _is_revalidated_graph_v1(port, ZDEXTokenomicsSafeLimitPortV1):
        return False
    policy = authority.execution_policy
    return (
        port.profile_root == authority.profile_root
        and port.route_release_id == authority.route_release_id
        and port.command_occurrence_id == authority.command_occurrence_id
        and port.global_pre_state_root == authority.global_pre_state_root
        and port.tokenomics_pre_state_root == authority.tokenomics_pre_state_root
        and port.selected_pool_id == policy.pool_id
        and port.quote_asset_id == policy.quote_asset_id
        and port.zdex_asset_id == policy.zdex_asset_id
        and port.price_policy_root == authority.price_policy_root
        and port.current_height == authority.current_height
    )


def _policy_matches_v1(authority: ZDEXTokenomicsBuybackAuthorityContextV1) -> bool:
    policy = authority.execution_policy
    return (
        policy.quote_asset_id < policy.zdex_asset_id
        and authority.spend_policy.quote_asset_id == policy.quote_asset_id
        and authority.hyperdeflation_policy.asset_id == policy.zdex_asset_id
    )


def _lane_well_formed_v1(
    candidate: ZDEXTokenomicsBuybackIntentInputV1,
    authority: ZDEXTokenomicsBuybackAuthorityContextV1,
) -> bool:
    supply = candidate.pre_state.supply
    policy = authority.hyperdeflation_policy
    return (
        len(candidate.pre_state.fee_allocation_states) <= authority.release.fee_asset_count_cap
        and supply.asset_id == policy.asset_id
        and supply.policy_root == policy.policy_root
        and supply.decimals <= policy.maximum_decimals
    )


def _select_quote_asset_v1(
    candidate: ZDEXTokenomicsBuybackIntentInputV1,
    authority: ZDEXTokenomicsBuybackAuthorityContextV1,
) -> _ZDEXTokenomicsSelectionV1 | ZDEXTokenomicsBuybackRejectCodeV1:
    quote_asset_id = authority.execution_policy.quote_asset_id
    state = candidate.pre_state
    fee_rows = tuple(row for row in state.fee_allocation_states if row.fee_asset_id == quote_asset_id)
    cadence_rows = tuple(
        row for row in state.buyback_cadence_states if row.quote_asset_id == quote_asset_id
    )
    if len(fee_rows) != 1 or len(cadence_rows) != 1:
        return ZDEXTokenomicsBuybackRejectCodeV1.SELECTION_MISMATCH
    fee_state, cadence = fee_rows[0], cadence_rows[0]
    if (
        fee_state.policy_root != authority.fee_policy.policy_root
        or cadence.policy_root != authority.spend_policy.policy_root
    ):
        return ZDEXTokenomicsBuybackRejectCodeV1.SELECTION_MISMATCH
    return _ZDEXTokenomicsSelectionV1(fee_state, cadence)


def _first_context_reject_v1(
    candidate: ZDEXTokenomicsBuybackIntentInputV1,
    authority: ZDEXTokenomicsBuybackAuthorityContextV1,
) -> ZDEXTokenomicsBuybackRejectCodeV1 | None:
    if not _release_matches_v1(authority):
        return ZDEXTokenomicsBuybackRejectCodeV1.RELEASE_MISMATCH
    if not _profile_matches_v1(authority):
        return ZDEXTokenomicsBuybackRejectCodeV1.PROFILE_MISMATCH
    _require_revalidated_graph_v1(candidate.pre_state)
    if authority.tokenomics_pre_state_root != candidate.pre_state.state_root:
        return ZDEXTokenomicsBuybackRejectCodeV1.STATE_COMMITMENT_MISMATCH
    if not _safe_limit_matches_v1(candidate, authority):
        return ZDEXTokenomicsBuybackRejectCodeV1.SAFETY_LIMIT_MISMATCH
    if not _policy_matches_v1(authority):
        return ZDEXTokenomicsBuybackRejectCodeV1.POLICY_MISMATCH
    if not _lane_well_formed_v1(candidate, authority):
        return ZDEXTokenomicsBuybackRejectCodeV1.LANE_MALFORMED
    return None


def _run_spend_kernel_v1(
    candidate: ZDEXTokenomicsBuybackIntentInputV1,
    authority: ZDEXTokenomicsBuybackAuthorityContextV1,
    selection: _ZDEXTokenomicsSelectionV1,
) -> ZDEXBuybackSpendAcceptedV1 | ZDEXTokenomicsBuybackRejectedV1:
    """Allocate the committed ingress and select the capped reserve spend."""

    port = candidate.safe_limit_port
    fee_context = ZDEXFeeAllocationContextV1(
        chain_id=authority.chain_id,
        deployment_root=authority.deployment_root,
        profile_root=authority.profile_root,
        writer_epoch=authority.writer_epoch,
        allocation_route_release_id=authority.route_release_id,
        authorized_buyback_route_release_id=authority.route_release_id,
        tokenomics_module_release_id=authority.tokenomics_module_release_id,
        command_occurrence_id=authority.command_occurrence_id,
        policy_root=authority.fee_policy.policy_root,
    )
    # The fee command is the committed ingress; no caller-selected fee budget exists.
    fee_command = ZDEXFeeAllocationCommandV1(selection.fee_state.fee_ingress_atoms)
    spend_context = ZDEXBuybackSpendContextV1(
        profile_root=authority.profile_root,
        route_release_id=authority.route_release_id,
        command_occurrence_id=authority.command_occurrence_id,
        expected_fee_pre_state_root=selection.fee_state.state_root,
        expected_cadence_pre_state_root=selection.cadence.state_root,
        safety_limit_binding_root=port.binding_root,
        quote_asset_id=authority.execution_policy.quote_asset_id,
        current_height=authority.current_height,
        route_safe_quote_limit_atoms=port.route_safe_quote_limit_atoms,
    )
    result = transition_zdex_buyback_spend_v1(
        authority.spend_policy,
        selection.cadence,
        authority.fee_policy,
        selection.fee_state,
        fee_context,
        fee_command,
        spend_context,
    )
    if type(result) is ZDEXBuybackSpendRejectedV1:
        return _reject(
            ZDEXTokenomicsBuybackRejectCodeV1.SPEND_REJECTED,
            candidate.pre_state,
            spend_code=result.code,
            fee_code=result.fee_code,
        )
    if type(result) is not ZDEXBuybackSpendAcceptedV1:
        raise TypeError("Tokenomics spend kernel result is not closed")
    return result


def _with_quote_asset_states_v1(
    state: ZDEXTokenomicsBuybackLaneStateV1,
    fee_state: ZDEXFeeStateV1,
    cadence: ZDEXBuybackSpendStateV1,
) -> ZDEXTokenomicsBuybackLaneStateV1:
    return replace(
        state,
        fee_allocation_states=tuple(
            fee_state if row.fee_asset_id == fee_state.fee_asset_id else row
            for row in state.fee_allocation_states
        ),
        buyback_cadence_states=tuple(
            cadence if row.quote_asset_id == cadence.quote_asset_id else row
            for row in state.buyback_cadence_states
        ),
    )


def _spend_effects_v1(
    spend: ZDEXBuybackSpendAcceptedV1,
    quote_asset_id: str,
) -> GlobalEconomicEffectPlanV1:
    allocation = spend.fee_allocation.effects
    reserve_debit = EconomicEffectRowV1(
        EconomicEffectKindV1.CUSTODY,
        FEE_BUYBACK_PRINCIPAL_V1,
        quote_asset_id,
        PROTOCOL_BUYBACK_CUSTODY_DOMAIN_V1,
        -spend.intent.quote_spend_atoms,
    )
    return GlobalEconomicEffectPlanV1(
        rows=tuple(sorted((*allocation.rows, reserve_debit), key=lambda row: row.key)),
        asset_conservation=allocation.asset_conservation,
        fee_conservation=allocation.fee_conservation,
        lane_writes=(),
        occurrence_consumptions=allocation.occurrence_consumptions,
        external_outbox_enqueue=(),
    )


def _quote_port_v2(
    authority: ZDEXTokenomicsBuybackAuthorityContextV1,
    spend: ZDEXBuybackSpendAcceptedV1,
    pre_state_root: str,
    spend_post_state_root: str,
    spend_effects: GlobalEconomicEffectPlanV1,
) -> ZDEXAtomicBuybackQuotePortV2:
    policy = authority.execution_policy
    return ZDEXAtomicBuybackQuotePortV2(
        profile_root=authority.profile_root,
        route_release_id=authority.route_release_id,
        command_occurrence_id=authority.command_occurrence_id,
        global_pre_state_root=authority.global_pre_state_root,
        producer_module_release_id=authority.tokenomics_module_release_id,
        consumer_module_release_id=authority.spot_module_release_id,
        producer_quote_pre_state_root=pre_state_root,
        producer_quote_post_state_root=spend_post_state_root,
        producer_quote_effect_plan_root=spend_effects.effect_plan_root,
        selected_pool_id=policy.pool_id,
        quote_asset_id=policy.quote_asset_id,
        amount_atoms=spend.intent.quote_spend_atoms,
    )


def _derive_intent_v1(
    candidate: ZDEXTokenomicsBuybackIntentInputV1,
) -> _ZDEXTokenomicsIntentFieldsV1 | ZDEXTokenomicsBuybackRejectedV1:
    """Run the ordered phase-A guards and derive the governed quote output."""

    if type(candidate) is not ZDEXTokenomicsBuybackIntentInputV1:
        raise TypeError("Tokenomics intent candidate must be exact typed data")
    pre_state = object.__getattribute__(candidate, "pre_state")
    if type(pre_state) is not ZDEXTokenomicsBuybackLaneStateV1:
        raise TypeError("Tokenomics intent pre-state must be exact typed data")
    authority_input = object.__getattribute__(candidate, "authority")
    if not _is_revalidated_graph_v1(authority_input, ZDEXTokenomicsBuybackAuthorityContextV1):
        return _reject(ZDEXTokenomicsBuybackRejectCodeV1.AUTHORITY_MALFORMED, pre_state)
    authority = cast(ZDEXTokenomicsBuybackAuthorityContextV1, authority_input)
    context_reject = _first_context_reject_v1(candidate, authority)
    if context_reject is not None:
        return _reject(context_reject, pre_state)
    selection = _select_quote_asset_v1(candidate, authority)
    if isinstance(selection, ZDEXTokenomicsBuybackRejectCodeV1):
        return _reject(selection, pre_state)
    spend_result = _run_spend_kernel_v1(candidate, authority, selection)
    if isinstance(spend_result, ZDEXTokenomicsBuybackRejectedV1):
        return spend_result
    if type(spend_result) is not ZDEXBuybackSpendAcceptedV1:
        raise TypeError("Tokenomics spend phase result is not closed")
    spend = spend_result
    spend_post_state = _with_quote_asset_states_v1(
        pre_state, spend.fee_post_state, spend.cadence_post_state
    )
    spend_effects = _spend_effects_v1(spend, authority.execution_policy.quote_asset_id)
    quote_output = _quote_port_v2(
        authority,
        spend,
        pre_state.state_root,
        spend_post_state.state_root,
        spend_effects,
    )
    return _ZDEXTokenomicsIntentFieldsV1(
        pre_state,
        spend_post_state,
        spend_effects,
        spend,
        quote_output,
        _context_root_v1(authority, candidate.safe_limit_port),
    )


def _spot_flow_id_v1(
    role: ZDEXSpotFlowRoleV1,
    obligation: ZDEXSpotTerminalObligationV1,
    asset: str,
    source_principal: str,
    destination_principal: str,
    amount_atoms: int,
) -> str:
    return ZDEXSpotFlowIdentityV1(
        role,
        obligation.context_root,
        obligation.selected_pool_id,
        asset,
        source_principal,
        destination_principal,
        amount_atoms,
    ).flow_id


def _purchase_port_reject_v1(
    obligation: object,
    authority: ZDEXTokenomicsBuybackAuthorityContextV1,
    intent: _ZDEXTokenomicsIntentFieldsV1,
) -> ZDEXTokenomicsBuybackRejectCodeV1 | None:
    """Bind the Spot obligation to the governed pool, assets, port, and exact q."""

    if not _is_revalidated_graph_v1(obligation, ZDEXSpotTerminalObligationV1):
        return ZDEXTokenomicsBuybackRejectCodeV1.PURCHASE_PORT_MISMATCH
    typed = cast(ZDEXSpotTerminalObligationV1, obligation)
    policy = authority.execution_policy
    burn_principal = zdex_occurrence_burn_port_v1(
        profile_root=authority.profile_root,
        route_release_id=authority.route_release_id,
        command_occurrence_id=authority.command_occurrence_id,
    )
    zdex_pool = zdex_pool_reserve_principal_v1(pool_id=policy.pool_id, asset_id=policy.zdex_asset_id)
    if (
        typed.consumer_module_release_id != authority.tokenomics_module_release_id
        or typed.burn_asset != policy.zdex_asset_id
        or typed.burn_principal != burn_principal
        or typed.selected_pool_id != policy.pool_id
        or typed.purchased_output_flow_id
        != _spot_flow_id_v1(
            ZDEXSpotFlowRoleV1.PURCHASED_ZDEX_OUTPUT,
            typed,
            policy.zdex_asset_id,
            zdex_pool,
            burn_principal,
            typed.purchased_atoms,
        )
    ):
        return ZDEXTokenomicsBuybackRejectCodeV1.PURCHASE_PORT_MISMATCH
    if typed.quote_input_flow_id != _spot_flow_id_v1(
        ZDEXSpotFlowRoleV1.QUOTE_INPUT,
        typed,
        policy.quote_asset_id,
        FEE_BUYBACK_PRINCIPAL_V1,
        intent.quote_output.destination_principal,
        intent.quote_output.amount_atoms,
    ):
        return ZDEXTokenomicsBuybackRejectCodeV1.QUOTE_FLOW_MISMATCH
    return None


def _derive_burn_amounts_v1(
    supply: ZDEXTokenomicsSupplyControlStateV1,
    policy: ZDEXHyperdeflationPolicyV1,
    purchased: int,
) -> _ZDEXTokenomicsBurnAmountsV1 | ZDEXTokenomicsBurnRejectCodeV1:
    """Burn exactly the purchased amount under retained-supply and epoch caps."""

    retained = retained_supply_atoms_v1(supply.live_supply_atoms, policy)
    ratio_headroom = supply.live_supply_atoms - retained
    epoch_headroom = supply.remaining_epoch_burn_cap_atoms
    if ratio_headroom == 0:
        return ZDEXTokenomicsBurnRejectCodeV1.RETAINED_SUPPLY_FLOOR_REACHED
    if epoch_headroom == 0:
        return ZDEXTokenomicsBurnRejectCodeV1.EPOCH_BURN_CAP_REACHED
    if purchased > min(ratio_headroom, epoch_headroom):
        return ZDEXTokenomicsBurnRejectCodeV1.BURN_EXCEEDS_CAPACITY
    return _ZDEXTokenomicsBurnAmountsV1(
        purchased,
        retained,
        supply.live_supply_atoms,
        supply.live_supply_atoms - purchased,
        epoch_headroom,
        epoch_headroom - purchased,
    )


def _build_effects_v1(
    intent: _ZDEXTokenomicsIntentFieldsV1,
    post_state: ZDEXTokenomicsBuybackLaneStateV1,
    zdex_asset_id: str,
    amounts: _ZDEXTokenomicsBurnAmountsV1,
) -> GlobalEconomicEffectPlanV1:
    spend = intent.spend_effects
    burn = EconomicEffectRowV1(
        EconomicEffectKindV1.BURN,
        ZDEX_SUPPLY_PRINCIPAL_V1,
        zdex_asset_id,
        PROTOCOL_SUPPLY_CUSTODY_DOMAIN_V1,
        -amounts.purchased,
    )
    supply_row = AssetConservationRowV1(
        zdex_asset_id,
        amounts.live_pre,
        amounts.live_post,
        amounts.live_pre,
        amounts.live_post,
        0,
        amounts.purchased,
    )
    return GlobalEconomicEffectPlanV1(
        rows=tuple(sorted((*spend.rows, burn), key=lambda row: row.key)),
        asset_conservation=tuple(
            sorted((*spend.asset_conservation, supply_row), key=lambda row: row.asset)
        ),
        fee_conservation=spend.fee_conservation,
        lane_writes=(
            LaneWriteV1(
                LaneIdV1.ZDEX_TOKENOMICS,
                intent.pre_state.state_root,
                post_state.state_root,
            ),
        ),
        occurrence_consumptions=spend.occurrence_consumptions,
        external_outbox_enqueue=(),
    )


def _build_journal_v1(
    intent: _ZDEXTokenomicsIntentFieldsV1,
    port: ZDEXTokenomicsSafeLimitPortV1,
    post_state: ZDEXTokenomicsBuybackLaneStateV1,
    effects: GlobalEconomicEffectPlanV1,
    ports: ZDEXTokenomicsPrivatePortsV1,
    zdex_asset_id: str,
    amounts: _ZDEXTokenomicsBurnAmountsV1,
) -> ZDEXTokenomicsBuybackJournalV1:
    occurrence = intent.spend.fee_allocation.occurrence
    spend_intent = intent.spend.intent
    quote = intent.quote_output
    return ZDEXTokenomicsBuybackJournalV1(
        intent.context_root,
        quote.producer_quote_pre_state_root,
        quote.producer_quote_post_state_root,
        post_state.state_root,
        quote.producer_quote_effect_plan_root,
        effects.effect_plan_root,
        quote.port_root,
        ports.ports_root,
        ports.burn_input.obligation_id,
        occurrence.occurrence_root,
        spend_intent.intent_root,
        port.binding_root,
        quote.selected_pool_id,
        quote.quote_asset_id,
        zdex_asset_id,
        port.current_height,
        occurrence.fee_charged_atoms,
        occurrence.buyback_quote_atoms,
        sum(row.allocation_atoms for row in occurrence.allocations[1:]),
        occurrence.carried_residue_atoms,
        spend_intent.buyback_reserve_before_atoms,
        intent.spend.fee_post_state.destination_balances[0].allocation_atoms,
        quote.amount_atoms,
        port.route_safe_quote_limit_atoms,
        ports.burn_input.purchased_atoms,
        amounts.purchased,
        amounts.live_pre,
        amounts.live_post,
        amounts.retained,
        amounts.cap_pre,
        amounts.cap_post,
    )


def _derive_transition_v1(
    candidate: ZDEXTokenomicsBuybackInputV1,
) -> _ZDEXTokenomicsBuybackAcceptedFieldsV1 | ZDEXTokenomicsBuybackRejectedV1:
    """Re-derive phase A, discharge the Spot obligation, and apply the exact burn."""

    if type(candidate) is not ZDEXTokenomicsBuybackInputV1:
        raise TypeError("Tokenomics buyback candidate must be exact typed data")
    intent = _derive_intent_v1(candidate.intent_input)
    if type(intent) is ZDEXTokenomicsBuybackRejectedV1:
        return intent
    if type(intent) is not _ZDEXTokenomicsIntentFieldsV1:
        raise TypeError("Tokenomics intent derivation result is not closed")
    pre_state = intent.pre_state
    authority = cast(ZDEXTokenomicsBuybackAuthorityContextV1, candidate.intent_input.authority)
    port_reject = _purchase_port_reject_v1(candidate.spot_obligation, authority, intent)
    if port_reject is not None:
        return _reject(port_reject, pre_state)
    obligation = cast(ZDEXSpotTerminalObligationV1, candidate.spot_obligation)
    zdex_asset_id = authority.execution_policy.zdex_asset_id
    amounts = _derive_burn_amounts_v1(
        pre_state.supply, authority.hyperdeflation_policy, obligation.purchased_atoms
    )
    if isinstance(amounts, ZDEXTokenomicsBurnRejectCodeV1):
        return _reject(ZDEXTokenomicsBuybackRejectCodeV1.BURN_REJECTED, pre_state, burn_code=amounts)
    post_supply = replace(
        pre_state.supply,
        live_supply_atoms=amounts.live_post,
        remaining_epoch_burn_cap_atoms=amounts.cap_post,
    )
    post_state = replace(intent.spend_post_state, supply=post_supply)
    effects = _build_effects_v1(intent, post_state, zdex_asset_id, amounts)
    ports = ZDEXTokenomicsPrivatePortsV1(intent.quote_output, obligation)
    journal = _build_journal_v1(
        intent,
        candidate.intent_input.safe_limit_port,
        post_state,
        effects,
        ports,
        zdex_asset_id,
        amounts,
    )
    return _ZDEXTokenomicsBuybackAcceptedFieldsV1(intent, post_state, effects, ports, journal)


def derive_zdex_tokenomics_buyback_intent_v1(
    candidate: ZDEXTokenomicsBuybackIntentInputV1,
) -> ZDEXTokenomicsBuybackIntentResultV1:
    """Return the revalidated governed quote output or an exact typed no-op rejection."""

    derived = _derive_intent_v1(candidate)
    if type(derived) is ZDEXTokenomicsBuybackRejectedV1:
        return derived
    if type(derived) is not _ZDEXTokenomicsIntentFieldsV1:
        raise TypeError("Tokenomics intent derivation result is not closed")
    return ZDEXTokenomicsBuybackIntentV1(_ACCEPTED_TOKEN_V1, candidate, derived)


def transition_zdex_tokenomics_buyback_v1(
    candidate: ZDEXTokenomicsBuybackInputV1,
) -> ZDEXTokenomicsBuybackResultV1:
    """Return a revalidated SHADOW result or an exact typed no-op rejection."""

    derived = _derive_transition_v1(candidate)
    if type(derived) is ZDEXTokenomicsBuybackRejectedV1:
        return derived
    if type(derived) is not _ZDEXTokenomicsBuybackAcceptedFieldsV1:
        raise TypeError("Tokenomics buyback derivation result is not closed")
    return ZDEXTokenomicsBuybackAcceptedV1(_ACCEPTED_TOKEN_V1, candidate, derived)


__all__ = [
    name
    for name in globals()
    if name.startswith("ZDEX") or name.startswith("transition_") or name.startswith("derive_")
]
