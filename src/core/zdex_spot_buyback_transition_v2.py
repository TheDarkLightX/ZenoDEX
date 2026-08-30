"""V2 Spot leaf for one same-occurrence ZDEX buyback purchase.

V2 consumes :class:`ZDEXAtomicBuybackQuotePortV2` directly.  It derives the
Spot state transition, canonical effect plan, flow identities, and an exact
Tokenomics burn obligation from that port.  The port deliberately contains no
receipt or journal root: a later route guest must authenticate the independently
proved Spot and Tokenomics journals and bind this exact port root.

This is a deterministic SHADOW functional core.  It does not verify a proof,
publish state, rotate a writer epoch, or grant value-moving authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeAlias, cast

from . import zdex_spot_buyback_transition_v1 as spot_v1
from .global_settlement_types_v1 import (
    MAX_DELTA_ATOMS_V1,
    GlobalEconomicEffectPlanV1,
    _require_atoms_u128,
    _require_nonnegative_int,
    _require_root,
    _require_token,
    hash_global_v1,
)
from .zdex_atomic_buyback_quote_port_v2 import ZDEXAtomicBuybackQuotePortV2
from .zdex_buyback_price_safety_v1 import VerifiedZDEXBuybackPriceSafetyV1
from .zdex_purchase_burn_route_types_v1 import zdex_occurrence_burn_port_v1

ZDEX_SPOT_BUYBACK_COORDINATES_SCHEMA_V2: Final = (
    "zenodex/zdex-spot-buyback-coordinates/v2"
)
ZDEX_SPOT_BUYBACK_CONTEXT_SCHEMA_V2: Final = (
    "zenodex/zdex-spot-buyback-transition-context/v2"
)
ZDEX_SPOT_PRICE_ENVELOPE_SCHEMA_V2: Final = (
    "zenodex/zdex-spot-price-envelope/v2"
)
ZDEX_SPOT_FLOW_SCHEMA_V2: Final = "zenodex/zdex-spot-buyback-flow/v2"
ZDEX_SPOT_PRIVATE_PORTS_SCHEMA_V2: Final = "zenodex/zdex-spot-private-ports/v2"
ZDEX_SPOT_TERMINAL_OBLIGATION_SCHEMA_V2: Final = (
    "zenodex/zdex-spot-terminal-obligation/v2"
)
ZDEX_SPOT_TRANSITION_JOURNAL_SCHEMA_V2: Final = (
    "zenodex/zdex-spot-buyback-transition-journal/v2"
)

_ACCEPTED_TOKEN_V2 = object()


class ZDEXSpotBuybackRejectCodeV2(str, Enum):
    """Closed V2 rejection vocabulary with exact no-op semantics."""

    INPUT_MALFORMED = "INPUT_MALFORMED"
    AUTHORITY_MALFORMED = "AUTHORITY_MALFORMED"
    RELEASE_MISMATCH = "RELEASE_MISMATCH"
    PROFILE_MISMATCH = "PROFILE_MISMATCH"
    STATE_COMMITMENT_MISMATCH = "STATE_COMMITMENT_MISMATCH"
    QUOTE_PORT_MISMATCH = "QUOTE_PORT_MISMATCH"
    ORACLE_MISMATCH = "ORACLE_MISMATCH"
    PRICE_SUBJECT_MISMATCH = "PRICE_SUBJECT_MISMATCH"
    POLICY_MISMATCH = "POLICY_MISMATCH"
    LANE_MALFORMED = "LANE_MALFORMED"
    SELECTION_MISMATCH = "SELECTION_MISMATCH"
    POOL_INACTIVE = "POOL_INACTIVE"
    AMOUNT_OUT_OF_RANGE = "AMOUNT_OUT_OF_RANGE"
    ARITHMETIC_OUT_OF_RANGE = "ARITHMETIC_OUT_OF_RANGE"
    FEE_CONSUMES_INPUT = "FEE_CONSUMES_INPUT"
    ZERO_OUTPUT = "ZERO_OUTPUT"
    MINIMUM_OUTPUT_MISMATCH = "MINIMUM_OUTPUT_MISMATCH"
    PRICE_UNSAFE = "PRICE_UNSAFE"


def _require_exact_root(value: object, *, name: str) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be exact str")
    return _require_root(value, name=name)


def _require_exact_token(value: object, *, name: str) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be exact str")
    return _require_token(value, name=name)


def _require_positive_effect_atoms(value: object, *, name: str) -> int:
    amount = _require_atoms_u128(value, name=name)
    if amount == 0 or amount > MAX_DELTA_ATOMS_V1:
        raise ValueError(f"{name} must fit a positive signed effect")
    return amount


def _revalidate_v1_lane_state_v2(state: spot_v1.ZDEXSpotLaneStateV1) -> None:
    """Re-run V1 constructors so forged frozen values cannot reach V2 math."""

    state.__post_init__()
    for pool in state.pools:
        pool.__post_init__()
        pool.definition.__post_init__()


def _revalidate_v1_authority_v2(
    authority: spot_v1.ZDEXSpotBuybackAuthorityContextV1,
) -> None:
    """Validate the complete V1 policy graph consumed by the V2 successor."""

    authority.__post_init__()
    release = authority.release
    release.__post_init__()
    for row in release.pool_creation_releases:
        row.__post_init__()
    for row in release.registered_sibling_curve_releases:
        row.__post_init__()
    authority.execution_policy.validate()
    authority.expected_pool_definition.__post_init__()
    authority.price_policy.__post_init__()
    authority.profile_authorization.__post_init__()
    authority.oracle_registry.__post_init__()
    for occurrence in authority.oracle_registry.occurrences:
        occurrence.__post_init__()
        occurrence.price.__post_init__()
    authority.oracle_occurrence.__post_init__()
    authority.oracle_occurrence.price.__post_init__()


@dataclass(frozen=True, slots=True)
class ZDEXSpotBuybackAuthorityContextV2:
    """V2 wrapper around unchanged V1 policy, profile, and Oracle facts.

    The wrapped type contains no predecessor quote journal or receipt root.
    V2 changes the cross-lane port contract while retaining the independently
    versioned V1 policy and state types.
    """

    stable_authority: spot_v1.ZDEXSpotBuybackAuthorityContextV1

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        if type(self.stable_authority) is not spot_v1.ZDEXSpotBuybackAuthorityContextV1:
            raise TypeError("Spot V2 authority requires exact V1 policy authority")
        spot_v1._require_exact_accepted_graph_v1(self.stable_authority)
        _revalidate_v1_authority_v2(self.stable_authority)


@dataclass(frozen=True, slots=True)
class ZDEXSpotBuybackCoordinatesV2:
    """Exact shared coordinates derived from one V2 quote port and Spot state."""

    profile_root: str
    route_release_id: str
    command_occurrence_id: str
    global_pre_state_root: str
    spot_pre_state_root: str
    producer_quote_pre_state_root: str
    producer_quote_post_state_root: str
    producer_quote_effect_plan_root: str
    quote_port_root: str

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        for field_name in (
            "profile_root",
            "route_release_id",
            "command_occurrence_id",
            "global_pre_state_root",
            "spot_pre_state_root",
            "producer_quote_pre_state_root",
            "producer_quote_post_state_root",
            "producer_quote_effect_plan_root",
            "quote_port_root",
        ):
            _require_exact_root(
                object.__getattribute__(self, field_name),
                name=f"Spot V2 coordinates {field_name}",
            )
        if self.producer_quote_pre_state_root == self.producer_quote_post_state_root:
            raise ValueError("Spot V2 producer quote phase must change state")

    @property
    def coordinates_root(self) -> str:
        self.validate()
        return hash_global_v1("zdex-spot-buyback-coordinates-v2", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        self.validate()
        return {
            "schema": ZDEX_SPOT_BUYBACK_COORDINATES_SCHEMA_V2,
            "profile_root": self.profile_root,
            "route_release_id": self.route_release_id,
            "command_occurrence_id": self.command_occurrence_id,
            "global_pre_state_root": self.global_pre_state_root,
            "spot_pre_state_root": self.spot_pre_state_root,
            "producer_quote_pre_state_root": self.producer_quote_pre_state_root,
            "producer_quote_post_state_root": self.producer_quote_post_state_root,
            "producer_quote_effect_plan_root": self.producer_quote_effect_plan_root,
            "quote_port_root": self.quote_port_root,
        }


@dataclass(frozen=True, slots=True)
class ZDEXSpotBuybackContextV2:
    """V2 execution context whose canonical root commits the V2 quote port."""

    coordinates: ZDEXSpotBuybackCoordinatesV2
    chain_id: str
    deployment_root: str
    profile_authorization_root: str
    writer_epoch: int
    current_height: int
    spot_module_release_id: str
    tokenomics_module_release_id: str
    release_root: str
    execution_policy_root: str
    price_policy_root: str
    oracle_registry_root: str
    oracle_occurrence_id: str

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        if type(self.coordinates) is not ZDEXSpotBuybackCoordinatesV2:
            raise TypeError("Spot V2 context coordinates must be exact typed data")
        self.coordinates.validate()
        _require_exact_token(self.chain_id, name="Spot V2 context chain id")
        for field_name in (
            "deployment_root",
            "profile_authorization_root",
            "spot_module_release_id",
            "tokenomics_module_release_id",
            "release_root",
            "execution_policy_root",
            "price_policy_root",
            "oracle_registry_root",
            "oracle_occurrence_id",
        ):
            _require_exact_root(
                object.__getattribute__(self, field_name),
                name=f"Spot V2 context {field_name}",
            )
        _require_nonnegative_int(self.writer_epoch, name="Spot V2 context writer epoch")
        _require_nonnegative_int(self.current_height, name="Spot V2 context current height")

    @property
    def context_root(self) -> str:
        self.validate()
        return hash_global_v1("zdex-spot-buyback-transition-context-v2", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        self.validate()
        return {
            "schema": ZDEX_SPOT_BUYBACK_CONTEXT_SCHEMA_V2,
            "coordinates": self.coordinates.to_canonical(),
            "coordinates_root": self.coordinates.coordinates_root,
            "quote_port_root": self.coordinates.quote_port_root,
            "chain_id": self.chain_id,
            "deployment_root": self.deployment_root,
            "profile_authorization_root": self.profile_authorization_root,
            "writer_epoch": self.writer_epoch,
            "current_height": self.current_height,
            "spot_module_release_id": self.spot_module_release_id,
            "tokenomics_module_release_id": self.tokenomics_module_release_id,
            "release_root": self.release_root,
            "execution_policy_root": self.execution_policy_root,
            "price_policy_root": self.price_policy_root,
            "oracle_registry_root": self.oracle_registry_root,
            "oracle_occurrence_id": self.oracle_occurrence_id,
        }


@dataclass(frozen=True, slots=True)
class ZDEXSpotPriceEnvelopeV2:
    """Price assertions bound to the same V2 quote-port coordinates as Spot."""

    coordinates: ZDEXSpotBuybackCoordinatesV2
    selected_pool_id: str
    oracle_occurrence_id: str
    oracle_finality_root: str
    quote_amount_atoms: int
    current_height: int
    oracle_observed_height: int
    oracle_quote_numerator_atoms: int
    oracle_zdex_denominator_atoms: int
    claimed_route_safe_quote_limit_atoms: int
    minimum_output_atoms: int

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        if type(self.coordinates) is not ZDEXSpotBuybackCoordinatesV2:
            raise TypeError("Spot V2 price envelope coordinates must be exact typed data")
        self.coordinates.validate()
        for field_name in (
            "selected_pool_id",
            "oracle_occurrence_id",
            "oracle_finality_root",
        ):
            _require_exact_root(
                object.__getattribute__(self, field_name),
                name=f"Spot V2 price envelope {field_name}",
            )
        for field_name in (
            "quote_amount_atoms",
            "oracle_quote_numerator_atoms",
            "oracle_zdex_denominator_atoms",
            "claimed_route_safe_quote_limit_atoms",
            "minimum_output_atoms",
        ):
            _require_atoms_u128(
                object.__getattribute__(self, field_name),
                name=f"Spot V2 price envelope {field_name}",
            )
        _require_nonnegative_int(self.current_height, name="Spot V2 price current height")
        _require_nonnegative_int(
            self.oracle_observed_height,
            name="Spot V2 price Oracle observed height",
        )


@dataclass(frozen=True, slots=True)
class ZDEXSpotBuybackInputV2:
    """Typed V2 command projection; malformed authority returns a typed no-op."""

    authority: object
    pre_state: spot_v1.ZDEXSpotLaneStateV1
    quote_port: ZDEXAtomicBuybackQuotePortV2
    price_envelope: ZDEXSpotPriceEnvelopeV2

    def __post_init__(self) -> None:
        self.validate_payload()

    def validate_payload(self) -> None:
        if type(self.pre_state) is not spot_v1.ZDEXSpotLaneStateV1:
            raise TypeError("Spot V2 input pre-state must be exact typed data")
        spot_v1._require_exact_accepted_graph_v1(self.pre_state)
        _revalidate_v1_lane_state_v2(self.pre_state)
        if type(self.quote_port) is not ZDEXAtomicBuybackQuotePortV2:
            raise TypeError("Spot V2 input quote port must be exact typed data")
        self.quote_port.validate()
        if type(self.price_envelope) is not ZDEXSpotPriceEnvelopeV2:
            raise TypeError("Spot V2 input price envelope must be exact typed data")
        self.price_envelope.validate()


@dataclass(frozen=True, slots=True)
class ZDEXSpotFlowIdentityV2:
    """One cross-lane movement identity bound to the V2 context and port root."""

    role: spot_v1.ZDEXSpotFlowRoleV1
    context: ZDEXSpotBuybackContextV2
    selected_pool_id: str
    asset: str
    source_principal: str
    destination_principal: str
    amount_atoms: int

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        if type(self.role) is not spot_v1.ZDEXSpotFlowRoleV1:
            raise TypeError("Spot V2 flow role is not closed")
        if type(self.context) is not ZDEXSpotBuybackContextV2:
            raise TypeError("Spot V2 flow context must be exact typed data")
        self.context.validate()
        for field_name in ("selected_pool_id", "asset"):
            _require_exact_root(
                object.__getattribute__(self, field_name),
                name=f"Spot V2 flow {field_name}",
            )
        for field_name in ("source_principal", "destination_principal"):
            _require_exact_token(
                object.__getattribute__(self, field_name),
                name=f"Spot V2 flow {field_name}",
            )
        _require_positive_effect_atoms(self.amount_atoms, name="Spot V2 flow amount")

    @property
    def flow_id(self) -> str:
        self.validate()
        return hash_global_v1("zdex-spot-buyback-flow-v2", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        self.validate()
        return {
            "schema": ZDEX_SPOT_FLOW_SCHEMA_V2,
            "role": self.role,
            "context_root": self.context.context_root,
            "coordinates_root": self.context.coordinates.coordinates_root,
            "quote_port_root": self.context.coordinates.quote_port_root,
            "selected_pool_id": self.selected_pool_id,
            "asset": self.asset,
            "source_principal": self.source_principal,
            "destination_principal": self.destination_principal,
            "amount_atoms": self.amount_atoms,
        }


@dataclass(frozen=True, slots=True)
class ZDEXSpotPrivatePortsV2:
    quote_input: ZDEXSpotFlowIdentityV2
    purchased_output: ZDEXSpotFlowIdentityV2

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        if (
            type(self.quote_input) is not ZDEXSpotFlowIdentityV2
            or type(self.purchased_output) is not ZDEXSpotFlowIdentityV2
        ):
            raise TypeError("Spot V2 private ports must be exact flow data")
        self.quote_input.validate()
        self.purchased_output.validate()
        if (
            self.quote_input.role is not spot_v1.ZDEXSpotFlowRoleV1.QUOTE_INPUT
            or self.purchased_output.role
            is not spot_v1.ZDEXSpotFlowRoleV1.PURCHASED_ZDEX_OUTPUT
            or self.quote_input.context.context_root
            != self.purchased_output.context.context_root
            or self.quote_input.selected_pool_id != self.purchased_output.selected_pool_id
        ):
            raise ValueError("Spot V2 private ports do not form one exact role pair")

    @property
    def ports_root(self) -> str:
        self.validate()
        return hash_global_v1(
            "zdex-spot-private-ports-v2",
            {
                "schema": ZDEX_SPOT_PRIVATE_PORTS_SCHEMA_V2,
                "context_root": self.quote_input.context.context_root,
                "quote_port_root": self.quote_input.context.coordinates.quote_port_root,
                "quote_input": self.quote_input.to_canonical(),
                "purchased_output": self.purchased_output.to_canonical(),
                "quote_input_flow_id": self.quote_input.flow_id,
                "purchased_output_flow_id": self.purchased_output.flow_id,
            },
        )


@dataclass(frozen=True, slots=True)
class ZDEXSpotTerminalObligationV2:
    """Exact same-occurrence obligation for Tokenomics to burn purchased ZDEX."""

    context: ZDEXSpotBuybackContextV2
    post_state_root: str
    consumer_module_release_id: str
    burn_asset: str
    burn_principal: str
    selected_pool_id: str
    quote_input_flow_id: str
    purchased_output_flow_id: str
    purchased_atoms: int

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        if type(self.context) is not ZDEXSpotBuybackContextV2:
            raise TypeError("Spot V2 terminal context must be exact typed data")
        self.context.validate()
        for field_name in (
            "post_state_root",
            "consumer_module_release_id",
            "burn_asset",
            "selected_pool_id",
            "quote_input_flow_id",
            "purchased_output_flow_id",
        ):
            _require_exact_root(
                object.__getattribute__(self, field_name),
                name=f"Spot V2 terminal {field_name}",
            )
        _require_exact_token(self.burn_principal, name="Spot V2 terminal burn principal")
        _require_positive_effect_atoms(self.purchased_atoms, name="Spot V2 terminal amount")

    @property
    def obligation_id(self) -> str:
        self.validate()
        return hash_global_v1("zdex-spot-terminal-obligation-v2", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        self.validate()
        return {
            "schema": ZDEX_SPOT_TERMINAL_OBLIGATION_SCHEMA_V2,
            "kind": "MUST_BURN_PURCHASED_ZDEX",
            "burn_domain": "ZDEX_TOKEN_SUPPLY",
            "context_root": self.context.context_root,
            "coordinates_root": self.context.coordinates.coordinates_root,
            "quote_port_root": self.context.coordinates.quote_port_root,
            "post_state_root": self.post_state_root,
            "consumer_module_release_id": self.consumer_module_release_id,
            "burn_asset": self.burn_asset,
            "burn_principal": self.burn_principal,
            "selected_pool_id": self.selected_pool_id,
            "quote_input_flow_id": self.quote_input_flow_id,
            "purchased_output_flow_id": self.purchased_output_flow_id,
            "purchased_atoms": self.purchased_atoms,
        }


@dataclass(frozen=True, slots=True)
class ZDEXSpotBuybackJournalV2:
    """Public V2 Spot transition projection with no predecessor receipt fields."""

    context: ZDEXSpotBuybackContextV2
    post_state_root: str
    effect_plan_root: str
    private_ports_root: str
    terminal_obligation_id: str
    selected_pool_id: str
    pool_definition_root: str
    quote_input_atoms: int
    fee_atoms: int
    net_input_atoms: int
    purchased_zdex_atoms: int
    route_safe_quote_limit_atoms: int
    minimum_output_atoms: int
    pre_quote_reserve_atoms: int
    post_quote_reserve_atoms: int
    pre_zdex_reserve_atoms: int
    post_zdex_reserve_atoms: int

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        if type(self.context) is not ZDEXSpotBuybackContextV2:
            raise TypeError("Spot V2 journal context must be exact typed data")
        self.context.validate()
        for field_name in (
            "post_state_root",
            "effect_plan_root",
            "private_ports_root",
            "terminal_obligation_id",
            "selected_pool_id",
            "pool_definition_root",
        ):
            _require_exact_root(
                object.__getattribute__(self, field_name),
                name=f"Spot V2 journal {field_name}",
            )
        for field_name in (
            "quote_input_atoms",
            "fee_atoms",
            "net_input_atoms",
            "purchased_zdex_atoms",
            "route_safe_quote_limit_atoms",
            "minimum_output_atoms",
            "pre_quote_reserve_atoms",
            "post_quote_reserve_atoms",
            "pre_zdex_reserve_atoms",
            "post_zdex_reserve_atoms",
        ):
            _require_atoms_u128(
                object.__getattribute__(self, field_name),
                name=f"Spot V2 journal {field_name}",
            )
        if (
            self.quote_input_atoms == 0
            or self.purchased_zdex_atoms == 0
            or self.quote_input_atoms != self.fee_atoms + self.net_input_atoms
            or self.post_quote_reserve_atoms
            != self.pre_quote_reserve_atoms + self.quote_input_atoms
            or self.post_zdex_reserve_atoms + self.purchased_zdex_atoms
            != self.pre_zdex_reserve_atoms
        ):
            raise ValueError("Spot V2 journal accounting projection is inconsistent")

    @property
    def journal_root(self) -> str:
        self.validate()
        return hash_global_v1("zdex-spot-buyback-transition-journal-v2", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        self.validate()
        return {
            "schema": ZDEX_SPOT_TRANSITION_JOURNAL_SCHEMA_V2,
            "context_root": self.context.context_root,
            "coordinates_root": self.context.coordinates.coordinates_root,
            "quote_port_root": self.context.coordinates.quote_port_root,
            "post_state_root": self.post_state_root,
            "effect_plan_root": self.effect_plan_root,
            "private_ports_root": self.private_ports_root,
            "terminal_obligation_id": self.terminal_obligation_id,
            "selected_pool_id": self.selected_pool_id,
            "pool_definition_root": self.pool_definition_root,
            "quote_input_atoms": self.quote_input_atoms,
            "fee_atoms": self.fee_atoms,
            "net_input_atoms": self.net_input_atoms,
            "purchased_zdex_atoms": self.purchased_zdex_atoms,
            "route_safe_quote_limit_atoms": self.route_safe_quote_limit_atoms,
            "minimum_output_atoms": self.minimum_output_atoms,
            "pre_quote_reserve_atoms": self.pre_quote_reserve_atoms,
            "post_quote_reserve_atoms": self.post_quote_reserve_atoms,
            "pre_zdex_reserve_atoms": self.pre_zdex_reserve_atoms,
            "post_zdex_reserve_atoms": self.post_zdex_reserve_atoms,
        }


@dataclass(frozen=True, slots=True)
class ZDEXSpotBuybackRejectedV2:
    code: ZDEXSpotBuybackRejectCodeV2
    pre_state: spot_v1.ZDEXSpotLaneStateV1
    post_state: spot_v1.ZDEXSpotLaneStateV1
    effects: GlobalEconomicEffectPlanV1 = GlobalEconomicEffectPlanV1.empty()
    context: None = None
    ports: None = None
    journal: None = None
    terminal_obligation: None = None

    def __post_init__(self) -> None:
        if type(self.code) is not ZDEXSpotBuybackRejectCodeV2:
            raise TypeError("Spot V2 reject code is not closed")
        if type(self.pre_state) is not spot_v1.ZDEXSpotLaneStateV1:
            raise TypeError("Spot V2 rejection pre-state must be exact typed data")
        if self.pre_state is not self.post_state or not self.effects.is_empty:
            raise ValueError("Spot V2 rejection must be an exact no-effect no-op")


@dataclass(frozen=True, slots=True)
class _ZDEXSpotBuybackAcceptedFieldsV2:
    pre_state: spot_v1.ZDEXSpotLaneStateV1
    post_state: spot_v1.ZDEXSpotLaneStateV1
    effects: GlobalEconomicEffectPlanV1
    context: ZDEXSpotBuybackContextV2
    ports: ZDEXSpotPrivatePortsV2
    journal: ZDEXSpotBuybackJournalV2
    terminal_obligation: ZDEXSpotTerminalObligationV2
    price_safety: VerifiedZDEXBuybackPriceSafetyV1

    def validate(self) -> None:
        for field_name in ("pre_state", "post_state", "effects", "price_safety"):
            spot_v1._require_exact_accepted_graph_v1(
                object.__getattribute__(self, field_name)
            )
        if type(self.context) is not ZDEXSpotBuybackContextV2:
            raise TypeError("Spot V2 accepted context must be exact typed data")
        if type(self.ports) is not ZDEXSpotPrivatePortsV2:
            raise TypeError("Spot V2 accepted ports must be exact typed data")
        if type(self.journal) is not ZDEXSpotBuybackJournalV2:
            raise TypeError("Spot V2 accepted journal must be exact typed data")
        if type(self.terminal_obligation) is not ZDEXSpotTerminalObligationV2:
            raise TypeError("Spot V2 accepted terminal must be exact typed data")
        self.context.validate()
        self.ports.validate()
        self.journal.validate()
        self.terminal_obligation.validate()
        if (
            self.ports.quote_input.context.context_root != self.context.context_root
            or self.journal.context.context_root != self.context.context_root
            or self.terminal_obligation.context.context_root != self.context.context_root
            or self.journal.private_ports_root != self.ports.ports_root
            or self.journal.terminal_obligation_id
            != self.terminal_obligation.obligation_id
        ):
            raise ValueError("Spot V2 accepted projections disagree on context or ports")


def _reject(
    code: ZDEXSpotBuybackRejectCodeV2,
    state: spot_v1.ZDEXSpotLaneStateV1,
) -> ZDEXSpotBuybackRejectedV2:
    return ZDEXSpotBuybackRejectedV2(code, state, state)


def _coordinates_for_v2(
    authority: spot_v1.ZDEXSpotBuybackAuthorityContextV1,
    pre_state: spot_v1.ZDEXSpotLaneStateV1,
    quote_port: ZDEXAtomicBuybackQuotePortV2,
) -> ZDEXSpotBuybackCoordinatesV2:
    """Derive all port coordinates from one immutable candidate snapshot."""

    quote_port.validate()
    return ZDEXSpotBuybackCoordinatesV2(
        profile_root=authority.profile_root,
        route_release_id=authority.route_release_id,
        command_occurrence_id=authority.command_occurrence_id,
        global_pre_state_root=authority.global_pre_state_root,
        spot_pre_state_root=pre_state.state_root,
        producer_quote_pre_state_root=quote_port.producer_quote_pre_state_root,
        producer_quote_post_state_root=quote_port.producer_quote_post_state_root,
        producer_quote_effect_plan_root=quote_port.producer_quote_effect_plan_root,
        quote_port_root=quote_port.port_root,
    )


def _context_for_v2(
    authority: spot_v1.ZDEXSpotBuybackAuthorityContextV1,
    coordinates: ZDEXSpotBuybackCoordinatesV2,
) -> ZDEXSpotBuybackContextV2:
    return ZDEXSpotBuybackContextV2(
        coordinates=coordinates,
        chain_id=authority.chain_id,
        deployment_root=authority.deployment_root,
        profile_authorization_root=authority.profile_authorization_root,
        writer_epoch=authority.writer_epoch,
        current_height=authority.current_height,
        spot_module_release_id=authority.spot_module_release_id,
        tokenomics_module_release_id=authority.tokenomics_module_release_id,
        release_root=authority.release.release_root,
        execution_policy_root=authority.execution_policy.policy_root,
        price_policy_root=authority.price_policy.policy_root,
        oracle_registry_root=authority.oracle_registry.registry_root,
        oracle_occurrence_id=authority.oracle_occurrence.occurrence_id,
    )


def _quote_matches_v2(
    candidate: ZDEXSpotBuybackInputV2,
    authority: spot_v1.ZDEXSpotBuybackAuthorityContextV1,
    coordinates: ZDEXSpotBuybackCoordinatesV2,
) -> bool:
    quote = candidate.quote_port
    policy = authority.execution_policy
    return (
        quote.profile_root == coordinates.profile_root
        and quote.route_release_id == coordinates.route_release_id
        and quote.command_occurrence_id == coordinates.command_occurrence_id
        and quote.global_pre_state_root == coordinates.global_pre_state_root
        and quote.producer_module_release_id == authority.tokenomics_module_release_id
        and quote.consumer_module_release_id == authority.spot_module_release_id
        and quote.selected_pool_id == policy.pool_id
        and quote.quote_asset_id == policy.quote_asset_id
        and quote.producer_quote_pre_state_root
        == coordinates.producer_quote_pre_state_root
        and quote.producer_quote_post_state_root
        == coordinates.producer_quote_post_state_root
        and quote.producer_quote_effect_plan_root
        == coordinates.producer_quote_effect_plan_root
        and quote.port_root == coordinates.quote_port_root
    )


def _price_subject_matches_v2(
    candidate: ZDEXSpotBuybackInputV2,
    authority: spot_v1.ZDEXSpotBuybackAuthorityContextV1,
    coordinates: ZDEXSpotBuybackCoordinatesV2,
) -> bool:
    envelope = candidate.price_envelope
    oracle = authority.oracle_occurrence
    return (
        envelope.coordinates.coordinates_root == coordinates.coordinates_root
        and envelope.coordinates.quote_port_root == coordinates.quote_port_root
        and envelope.selected_pool_id == authority.execution_policy.pool_id
        and envelope.oracle_occurrence_id == oracle.occurrence_id
        and envelope.oracle_finality_root == oracle.finality_root
        and envelope.quote_amount_atoms == candidate.quote_port.amount_atoms
        and envelope.current_height == authority.current_height
        and envelope.oracle_observed_height == oracle.price.observed_height
        and envelope.oracle_quote_numerator_atoms == oracle.price.quote_numerator_atoms
        and envelope.oracle_zdex_denominator_atoms == oracle.price.zdex_denominator_atoms
    )


def _v1_math_input_view(
    candidate: ZDEXSpotBuybackInputV2,
) -> spot_v1.ZDEXSpotBuybackInputV1:
    """Expose only the V1 helper fields shared by the V2 math contract.

    This is a static view rather than a constructed V1 input.  The invoked
    V1 helpers read ``pre_state``, ``quote_port.amount_atoms``, and the price
    envelope arithmetic fields.  They never read a predecessor journal or
    receipt-binding root, so no synthetic legacy data is introduced.
    """

    return cast(spot_v1.ZDEXSpotBuybackInputV1, candidate)


def _map_v1_reject(code: spot_v1.ZDEXSpotBuybackRejectCodeV1) -> ZDEXSpotBuybackRejectCodeV2:
    if type(code) is not spot_v1.ZDEXSpotBuybackRejectCodeV1:
        raise TypeError("Spot V2 V1-helper rejection is not closed")
    return ZDEXSpotBuybackRejectCodeV2(code.value)


@dataclass(frozen=True, slots=True)
class _ZDEXSpotAcceptedBuildV2:
    """Fresh, fully derived values required by the final V2 publication shape."""

    candidate: ZDEXSpotBuybackInputV2
    authority: spot_v1.ZDEXSpotBuybackAuthorityContextV1
    context: ZDEXSpotBuybackContextV2
    selection: spot_v1._ZDEXSpotSelectedPoolV1
    amounts: spot_v1._ZDEXSpotSwapAmountsV1
    post_state: spot_v1.ZDEXSpotLaneStateV1
    updated_pool: spot_v1.ZDEXSpotPoolV1
    effects: GlobalEconomicEffectPlanV1
    quote_pool_principal: str
    zdex_pool_principal: str


def _build_ports_and_terminal_v2(
    build: _ZDEXSpotAcceptedBuildV2,
) -> tuple[ZDEXSpotPrivatePortsV2, ZDEXSpotTerminalObligationV2]:
    policy = build.authority.execution_policy
    burn_principal = zdex_occurrence_burn_port_v1(
        profile_root=build.context.coordinates.profile_root,
        route_release_id=build.context.coordinates.route_release_id,
        command_occurrence_id=build.context.coordinates.command_occurrence_id,
    )
    quote_flow = ZDEXSpotFlowIdentityV2(
        spot_v1.ZDEXSpotFlowRoleV1.QUOTE_INPUT,
        build.context,
        build.selection.pool.pool_id,
        policy.quote_asset_id,
        build.candidate.quote_port.source_principal,
        build.quote_pool_principal,
        build.amounts.gross,
    )
    purchased_flow = ZDEXSpotFlowIdentityV2(
        spot_v1.ZDEXSpotFlowRoleV1.PURCHASED_ZDEX_OUTPUT,
        build.context,
        build.selection.pool.pool_id,
        policy.zdex_asset_id,
        build.zdex_pool_principal,
        burn_principal,
        build.amounts.purchased,
    )
    ports = ZDEXSpotPrivatePortsV2(quote_flow, purchased_flow)
    terminal = ZDEXSpotTerminalObligationV2(
        build.context,
        build.post_state.state_root,
        build.authority.tokenomics_module_release_id,
        policy.zdex_asset_id,
        burn_principal,
        build.selection.pool.pool_id,
        quote_flow.flow_id,
        purchased_flow.flow_id,
        build.amounts.purchased,
    )
    return ports, terminal


def _build_journal_v2(
    build: _ZDEXSpotAcceptedBuildV2,
    ports: ZDEXSpotPrivatePortsV2,
    terminal: ZDEXSpotTerminalObligationV2,
) -> ZDEXSpotBuybackJournalV2:
    journal = ZDEXSpotBuybackJournalV2(
        build.context,
        build.post_state.state_root,
        build.effects.effect_plan_root,
        ports.ports_root,
        terminal.obligation_id,
        build.selection.pool.pool_id,
        build.selection.pool.definition.definition_root,
        build.amounts.gross,
        build.amounts.fee,
        build.amounts.net,
        build.amounts.purchased,
        build.candidate.price_envelope.claimed_route_safe_quote_limit_atoms,
        build.candidate.price_envelope.minimum_output_atoms,
        build.selection.pool.reserve0_atoms,
        build.updated_pool.reserve0_atoms,
        build.selection.pool.reserve1_atoms,
        build.updated_pool.reserve1_atoms,
    )
    return journal


def _first_context_reject_v2(
    candidate: ZDEXSpotBuybackInputV2,
    authority: spot_v1.ZDEXSpotBuybackAuthorityContextV1,
    coordinates: ZDEXSpotBuybackCoordinatesV2,
) -> ZDEXSpotBuybackRejectCodeV2 | None:
    if not spot_v1._release_matches_v1(authority):
        return ZDEXSpotBuybackRejectCodeV2.RELEASE_MISMATCH
    if not spot_v1._profile_matches_v1(authority):
        return ZDEXSpotBuybackRejectCodeV2.PROFILE_MISMATCH
    if authority.spot_pre_state_root != candidate.pre_state.state_root:
        return ZDEXSpotBuybackRejectCodeV2.STATE_COMMITMENT_MISMATCH
    if not _quote_matches_v2(candidate, authority, coordinates):
        return ZDEXSpotBuybackRejectCodeV2.QUOTE_PORT_MISMATCH
    if not spot_v1._oracle_matches_v1(authority):
        return ZDEXSpotBuybackRejectCodeV2.ORACLE_MISMATCH
    if not _price_subject_matches_v2(candidate, authority, coordinates):
        return ZDEXSpotBuybackRejectCodeV2.PRICE_SUBJECT_MISMATCH
    if not spot_v1._policy_matches_v1(authority):
        return ZDEXSpotBuybackRejectCodeV2.POLICY_MISMATCH
    if not spot_v1._lane_well_formed(authority.release, candidate.pre_state):
        return ZDEXSpotBuybackRejectCodeV2.LANE_MALFORMED
    return None


def _admit_candidate_v2(
    candidate: ZDEXSpotBuybackInputV2,
    pre_state: spot_v1.ZDEXSpotLaneStateV1,
) -> spot_v1.ZDEXSpotBuybackAuthorityContextV1 | ZDEXSpotBuybackRejectedV2:
    try:
        candidate.validate_payload()
    except (TypeError, ValueError):
        return _reject(ZDEXSpotBuybackRejectCodeV2.INPUT_MALFORMED, pre_state)
    if type(candidate.authority) is not ZDEXSpotBuybackAuthorityContextV2:
        return _reject(ZDEXSpotBuybackRejectCodeV2.AUTHORITY_MALFORMED, pre_state)
    try:
        candidate.authority.validate()
    except (TypeError, ValueError):
        return _reject(ZDEXSpotBuybackRejectCodeV2.AUTHORITY_MALFORMED, pre_state)
    return candidate.authority.stable_authority


def _run_stable_v1_math_v2(
    candidate: ZDEXSpotBuybackInputV2,
    authority: spot_v1.ZDEXSpotBuybackAuthorityContextV1,
    pre_state: spot_v1.ZDEXSpotLaneStateV1,
) -> (
    tuple[
        spot_v1._ZDEXSpotSelectedPoolV1,
        spot_v1._ZDEXSpotSwapAmountsV1,
        VerifiedZDEXBuybackPriceSafetyV1,
    ]
    | ZDEXSpotBuybackRejectedV2
):
    """Run the explicit V1 CPMM and price helpers over the V2 port view."""

    math_input = _v1_math_input_view(candidate)
    selection = spot_v1._select_pool_v1(math_input, authority)
    if type(selection) is spot_v1.ZDEXSpotBuybackRejectCodeV1:
        return _reject(_map_v1_reject(selection), pre_state)
    amounts = spot_v1._derive_swap_amounts_v1(math_input, authority, selection.pool)
    if type(amounts) is spot_v1.ZDEXSpotBuybackRejectCodeV1:
        return _reject(_map_v1_reject(amounts), pre_state)
    price_safety = spot_v1._verify_price_safety_v1(
        math_input,
        authority,
        selection.pool,
        amounts,
    )
    if type(price_safety) is spot_v1.ZDEXSpotBuybackRejectCodeV1:
        return _reject(_map_v1_reject(price_safety), pre_state)
    return selection, amounts, price_safety


def _derive_zdex_spot_buyback_v2(
    candidate: ZDEXSpotBuybackInputV2,
) -> _ZDEXSpotBuybackAcceptedFieldsV2 | ZDEXSpotBuybackRejectedV2:
    """Derive one V2 Spot projection or an exact typed no-op rejection."""

    if type(candidate) is not ZDEXSpotBuybackInputV2:
        raise TypeError("Spot V2 buyback candidate must be exact typed data")
    if type(candidate.pre_state) is not spot_v1.ZDEXSpotLaneStateV1:
        raise TypeError("Spot V2 candidate has no valid no-op state")
    pre_state = candidate.pre_state
    authority_or_rejection = _admit_candidate_v2(candidate, pre_state)
    if type(authority_or_rejection) is ZDEXSpotBuybackRejectedV2:
        return authority_or_rejection
    authority = authority_or_rejection
    coordinates = _coordinates_for_v2(authority, pre_state, candidate.quote_port)
    context_reject = _first_context_reject_v2(candidate, authority, coordinates)
    if context_reject is not None:
        return _reject(context_reject, pre_state)
    math_or_rejection = _run_stable_v1_math_v2(candidate, authority, pre_state)
    if type(math_or_rejection) is ZDEXSpotBuybackRejectedV2:
        return math_or_rejection
    selection, amounts, price_safety = cast(
        tuple[
            spot_v1._ZDEXSpotSelectedPoolV1,
            spot_v1._ZDEXSpotSwapAmountsV1,
            VerifiedZDEXBuybackPriceSafetyV1,
        ],
        math_or_rejection,
    )
    context = _context_for_v2(authority, coordinates)
    post_state, updated = spot_v1._build_post_state_v1(pre_state, selection, amounts)
    effects, quote_pool, zdex_pool = spot_v1._build_effects_v1(
        pre_state,
        post_state,
        selection.pool,
        authority,
        amounts,
    )
    build = _ZDEXSpotAcceptedBuildV2(
        candidate,
        authority,
        context,
        selection,
        amounts,
        post_state,
        updated,
        effects,
        quote_pool,
        zdex_pool,
    )
    ports, terminal = _build_ports_and_terminal_v2(build)
    journal = _build_journal_v2(build, ports, terminal)
    return _ZDEXSpotBuybackAcceptedFieldsV2(
        pre_state,
        post_state,
        effects,
        context,
        ports,
        journal,
        terminal,
        price_safety,
    )


def _accepted_fields_match_v2(
    expected: _ZDEXSpotBuybackAcceptedFieldsV2,
    supplied: _ZDEXSpotBuybackAcceptedFieldsV2,
) -> bool:
    """Compare only validated exact graphs, avoiding hostile ``__eq__`` values."""

    expected.validate()
    supplied.validate()
    return (
        spot_v1._exact_accepted_graph_matches_v1(expected.pre_state, supplied.pre_state)
        and spot_v1._exact_accepted_graph_matches_v1(expected.post_state, supplied.post_state)
        and spot_v1._exact_accepted_graph_matches_v1(expected.effects, supplied.effects)
        and expected.context.to_canonical() == supplied.context.to_canonical()
        and expected.ports.quote_input.to_canonical()
        == supplied.ports.quote_input.to_canonical()
        and expected.ports.purchased_output.to_canonical()
        == supplied.ports.purchased_output.to_canonical()
        and expected.journal.to_canonical() == supplied.journal.to_canonical()
        and expected.terminal_obligation.to_canonical()
        == supplied.terminal_obligation.to_canonical()
        and spot_v1._exact_accepted_graph_matches_v1(
            expected.price_safety,
            supplied.price_safety,
        )
    )


def _require_accepted_projection_types_v2(
    subject: object,
    fields: object,
) -> tuple[ZDEXSpotBuybackInputV2, _ZDEXSpotBuybackAcceptedFieldsV2]:
    if type(subject) is not ZDEXSpotBuybackInputV2:
        raise TypeError("Spot V2 accepted subject is not closed")
    if type(subject.authority) is not ZDEXSpotBuybackAuthorityContextV2:
        raise TypeError("Spot V2 accepted authority is not closed")
    subject.validate_payload()
    subject.authority.validate()
    if type(fields) is not _ZDEXSpotBuybackAcceptedFieldsV2:
        raise TypeError("Spot V2 accepted fields are not closed")
    fields.validate()
    return subject, fields


class ZDEXSpotBuybackAcceptedV2:
    """Locally rederived SHADOW result; it is not publication authority."""

    _subject: ZDEXSpotBuybackInputV2
    _fields: _ZDEXSpotBuybackAcceptedFieldsV2
    __slots__ = ("_subject", "_fields")

    def __init__(
        self,
        token: object,
        subject: ZDEXSpotBuybackInputV2,
        fields: _ZDEXSpotBuybackAcceptedFieldsV2,
    ) -> None:
        if token is not _ACCEPTED_TOKEN_V2:
            raise TypeError("Spot V2 accepted result requires local rederivation")
        subject, fields = _require_accepted_projection_types_v2(subject, fields)
        expected = _derive_zdex_spot_buyback_v2(subject)
        if type(expected) is not _ZDEXSpotBuybackAcceptedFieldsV2 or not _accepted_fields_match_v2(
            expected,
            fields,
        ):
            raise ValueError("Spot V2 accepted projection does not rederive")
        object.__setattr__(self, "_subject", subject)
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("Spot V2 accepted result is immutable")

    @property
    def pre_state(self) -> spot_v1.ZDEXSpotLaneStateV1:
        return self._fields.pre_state

    @property
    def post_state(self) -> spot_v1.ZDEXSpotLaneStateV1:
        return self._fields.post_state

    @property
    def effects(self) -> GlobalEconomicEffectPlanV1:
        return self._fields.effects

    @property
    def context(self) -> ZDEXSpotBuybackContextV2:
        return self._fields.context

    @property
    def quote_port_root(self) -> str:
        return self.context.coordinates.quote_port_root

    @property
    def ports(self) -> ZDEXSpotPrivatePortsV2:
        return self._fields.ports

    @property
    def journal(self) -> ZDEXSpotBuybackJournalV2:
        return self._fields.journal

    @property
    def terminal_obligation(self) -> ZDEXSpotTerminalObligationV2:
        return self._fields.terminal_obligation

    @property
    def price_safety(self) -> VerifiedZDEXBuybackPriceSafetyV1:
        return self._fields.price_safety

    def validate(self) -> None:
        subject, fields = _require_accepted_projection_types_v2(
            object.__getattribute__(self, "_subject"),
            object.__getattribute__(self, "_fields"),
        )
        expected = _derive_zdex_spot_buyback_v2(subject)
        if type(expected) is not _ZDEXSpotBuybackAcceptedFieldsV2 or not _accepted_fields_match_v2(
            expected,
            fields,
        ):
            raise ValueError("Spot V2 accepted projection no longer rederives")


ZDEXSpotBuybackResultV2: TypeAlias = ZDEXSpotBuybackAcceptedV2 | ZDEXSpotBuybackRejectedV2


def transition_zdex_spot_buyback_v2(
    candidate: ZDEXSpotBuybackInputV2,
) -> ZDEXSpotBuybackResultV2:
    """Run V2 Spot math and return a revalidated result or exact no-op.

    Units are integer atoms.  Accepted output conserves the two local pool
    reserves, binds the V2 quote-port root through every derived object, and
    emits an obligation for the same-occurrence Tokenomics burn.  This function
    is deterministic and performs no I/O, proof verification, or publication.
    """

    derived = _derive_zdex_spot_buyback_v2(candidate)
    if type(derived) is ZDEXSpotBuybackRejectedV2:
        return derived
    if type(derived) is not _ZDEXSpotBuybackAcceptedFieldsV2:
        raise TypeError("Spot V2 buyback derivation result is not closed")
    return ZDEXSpotBuybackAcceptedV2(_ACCEPTED_TOKEN_V2, candidate, derived)


__all__ = [name for name in globals() if name.startswith("ZDEX") or name.startswith("transition_")]
