"""Bounded Spot-lane transition for one governed ZDEX buy-and-burn.

The pure transition derives purchased ZDEX from one canonical CPMM pool.  It
never accepts purchased output, pool balances, or an effect plan as authority.
Accepted output retains a typed obligation for the Tokenomics lane to burn the
exact purchased amount in the same command occurrence.

This module is SHADOW research evidence.  It verifies no receipt, composes no
route, publishes no state, and grants no value-moving authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from dataclasses import fields as dataclass_fields
from enum import Enum
from typing import Final, TypeAlias, cast

from .global_settlement_types_v1 import (
    MAX_ATOMS_V1,
    MAX_DELTA_ATOMS_V1,
    MAX_U64_V1,
    ZERO_ROOT_V1,
    AssetConservationRowV1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    ExternalOutboxEnqueueV1,
    FeeConservationRowV1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    LaneWriteV1,
    ReleaseStatusV1,
    _require_atoms_u128,
    _require_nonnegative_int,
    _require_root,
    _require_token,
    hash_global_v1,
)
from .zdex_buyback_price_safety_v1 import (
    BASIS_POINTS_V1,
    VerifiedZDEXBuybackPriceSafetyV1,
    ZDEXBuybackOraclePriceOccurrenceV1,
    ZDEXBuybackPriceSafetyObservationV1,
    ZDEXBuybackPriceSafetyPolicyV1,
    ZDEXBuybackPriceSafetyRejectedV1,
    _VerifiedZDEXBuybackPriceSafetyFieldsV1,
    verify_zdex_buyback_price_safety_v1,
)
from .zdex_fee_allocation_types_v1 import FEE_BUYBACK_PRINCIPAL_V1
from .zdex_purchase_burn_route_types_v1 import (
    AMM_POOL_CUSTODY_DOMAIN_V1,
    ZDEXBuybackExecutionPolicyV1,
    zdex_occurrence_burn_port_v1,
    zdex_pool_reserve_principal_v1,
)

ZDEX_SPOT_BUYBACK_RELEASE_SCHEMA_V1: Final = "zenodex/zdex-spot-buyback-release/v1"
ZDEX_SPOT_POOL_DEFINITION_SCHEMA_V1: Final = "zenodex/zdex-spot-pool-definition/v1"
ZDEX_SPOT_POOL_SCHEMA_V1: Final = "zenodex/zdex-spot-pool/v1"
ZDEX_SPOT_LANE_STATE_SCHEMA_V1: Final = "zenodex/zdex-spot-lane-state/v1"
ZDEX_SPOT_PROFILE_AUTHORIZATION_SCHEMA_V1: Final = (
    "zenodex/zdex-spot-buyback-profile-authorization/v1"
)
ZDEX_SPOT_ORACLE_REGISTRY_SCHEMA_V1: Final = "zenodex/zdex-spot-oracle-registry/v1"
ZDEX_SPOT_QUOTE_INPUT_SCHEMA_V1: Final = "zenodex/zdex-spot-quote-input/v1"
ZDEX_SPOT_PRICE_ENVELOPE_SCHEMA_V1: Final = "zenodex/zdex-spot-price-envelope/v1"
ZDEX_SPOT_FLOW_SCHEMA_V1: Final = "zenodex/zdex-spot-buyback-flow/v1"
ZDEX_SPOT_PRIVATE_PORTS_SCHEMA_V1: Final = "zenodex/zdex-spot-private-ports/v1"
ZDEX_SPOT_TERMINAL_OBLIGATION_SCHEMA_V1: Final = (
    "zenodex/zdex-spot-terminal-obligation/v1"
)
ZDEX_SPOT_TRANSITION_JOURNAL_SCHEMA_V1: Final = (
    "zenodex/zdex-spot-buyback-transition-journal/v1"
)

ZDEX_SPOT_RESERVE_CAP_ATOMS_V1: Final = 3_000_000_000
ZDEX_SPOT_SWAP_CAP_ATOMS_V1: Final = 3_000_000_000
ZDEX_SPOT_POOL_COUNT_CAP_V1: Final = 64
CPMM_V8_EXACT_IN_CURVE_V1: Final = "CPMM_V8_EXACT_IN"
_ACCEPTED_TOKEN_V1 = object()
_ACCEPTED_GRAPH_NODE_CAP_V1: Final = 4_096
_ACCEPTED_GRAPH_DEPTH_CAP_V1: Final = 64


class ZDEXSpotPoolStatusV1(str, Enum):
    ACTIVE = "ACTIVE"
    FROZEN = "FROZEN"
    DISABLED = "DISABLED"


class ZDEXSpotCurveKindV1(str, Enum):
    CPMM_V8_EXACT_IN = CPMM_V8_EXACT_IN_CURVE_V1
    REGISTERED_OTHER = "REGISTERED_OTHER"


class ZDEXSpotOracleStatusV1(str, Enum):
    PENDING = "PENDING"
    FINAL = "FINAL"
    DISPUTED = "DISPUTED"


class ZDEXSpotFlowRoleV1(str, Enum):
    QUOTE_INPUT = "QUOTE_INPUT"
    PURCHASED_ZDEX_OUTPUT = "PURCHASED_ZDEX_OUTPUT"


class ZDEXSpotBuybackRejectCodeV1(str, Enum):
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


@dataclass(frozen=True, slots=True, order=True)
class ZDEXSpotRegisteredCurveReleaseV1:
    release_id: str
    status: ReleaseStatusV1

    def __post_init__(self) -> None:
        _require_root(self.release_id, name="Spot curve release id")
        if type(self.status) is not ReleaseStatusV1:
            raise TypeError("Spot curve release status is not closed")

    def to_canonical(self) -> dict[str, object]:
        return {"release_id": self.release_id, "status": self.status}


@dataclass(frozen=True, slots=True, order=True)
class ZDEXSpotPoolCreationReleaseV1:
    module_release_id: str
    status: ReleaseStatusV1

    def __post_init__(self) -> None:
        _require_root(self.module_release_id, name="Spot pool creation module release id")
        if type(self.status) is not ReleaseStatusV1:
            raise TypeError("Spot pool creation release status is not closed")

    def to_canonical(self) -> dict[str, object]:
        return {"module_release_id": self.module_release_id, "status": self.status}


@dataclass(frozen=True, slots=True)
class ZDEXSpotBuybackReleaseV1:
    spot_module_release_id: str
    tokenomics_module_release_id: str
    route_release_id: str
    cpmm_curve_release_id: str
    protocol_fee_share_bps: int
    reserve_cap_atoms: int
    swap_cap_atoms: int
    pool_count_cap: int
    pool_creation_releases: tuple[ZDEXSpotPoolCreationReleaseV1, ...]
    registered_sibling_curve_releases: tuple[ZDEXSpotRegisteredCurveReleaseV1, ...]

    def __post_init__(self) -> None:
        for name in (
            "spot_module_release_id",
            "tokenomics_module_release_id",
            "route_release_id",
            "cpmm_curve_release_id",
        ):
            _require_root(getattr(self, name), name=f"Spot buyback {name}")
        for name in (
            "protocol_fee_share_bps",
            "reserve_cap_atoms",
            "swap_cap_atoms",
            "pool_count_cap",
        ):
            _require_nonnegative_int(getattr(self, name), name=f"Spot buyback {name}")
        if type(self.pool_creation_releases) is not tuple or any(
            type(item) is not ZDEXSpotPoolCreationReleaseV1
            for item in self.pool_creation_releases
        ):
            raise TypeError("Spot pool creation releases must be an exact tuple")
        creation_ids = tuple(row.module_release_id for row in self.pool_creation_releases)
        if creation_ids != tuple(sorted(set(creation_ids))) or not creation_ids:
            raise ValueError("Spot pool creation releases must be nonempty and ordered")
        if type(self.registered_sibling_curve_releases) is not tuple or any(
            type(item) is not ZDEXSpotRegisteredCurveReleaseV1
            for item in self.registered_sibling_curve_releases
        ):
            raise TypeError("Spot sibling curve releases must be an exact tuple")
        ids = tuple(row.release_id for row in self.registered_sibling_curve_releases)
        if ids != tuple(sorted(set(ids))):
            raise ValueError("Spot sibling curve releases must be canonically ordered")

    @property
    def release_root(self) -> str:
        return hash_global_v1("zdex-spot-buyback-release-v1", self.to_canonical())

    @property
    def is_bounded_v1(self) -> bool:
        return (
            self.protocol_fee_share_bps == 0
            and self.reserve_cap_atoms == ZDEX_SPOT_RESERVE_CAP_ATOMS_V1
            and self.swap_cap_atoms == ZDEX_SPOT_SWAP_CAP_ATOMS_V1
            and self.pool_count_cap == ZDEX_SPOT_POOL_COUNT_CAP_V1
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ZDEX_SPOT_BUYBACK_RELEASE_SCHEMA_V1,
            "spot_module_release_id": self.spot_module_release_id,
            "tokenomics_module_release_id": self.tokenomics_module_release_id,
            "route_release_id": self.route_release_id,
            "cpmm_curve_release_id": self.cpmm_curve_release_id,
            "protocol_fee_share_bps": self.protocol_fee_share_bps,
            "reserve_cap_atoms": self.reserve_cap_atoms,
            "swap_cap_atoms": self.swap_cap_atoms,
            "pool_count_cap": self.pool_count_cap,
            "pool_creation_releases": self.pool_creation_releases,
            "registered_sibling_curve_releases": self.registered_sibling_curve_releases,
        }


@dataclass(frozen=True, slots=True)
class ZDEXSpotPoolDefinitionV1:
    asset0: str
    asset1: str
    fee_bps: int
    curve_kind: ZDEXSpotCurveKindV1
    curve_release_id: str
    curve_params_root: str

    def __post_init__(self) -> None:
        _require_root(self.asset0, name="Spot pool asset0")
        _require_root(self.asset1, name="Spot pool asset1")
        _require_nonnegative_int(self.fee_bps, name="Spot pool fee bps")
        if type(self.curve_kind) is not ZDEXSpotCurveKindV1:
            raise TypeError("Spot pool curve kind is not closed")
        _require_root(self.curve_release_id, name="Spot pool curve release id")
        _require_root(self.curve_params_root, name="Spot pool curve params", allow_zero=True)

    @property
    def definition_root(self) -> str:
        return hash_global_v1("zdex-spot-pool-definition-v1", self.to_canonical())

    @property
    def pool_id(self) -> str:
        return hash_global_v1(
            "zdex-spot-pool-id-v1",
            {"schema": ZDEX_SPOT_POOL_DEFINITION_SCHEMA_V1, "definition": self},
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ZDEX_SPOT_POOL_DEFINITION_SCHEMA_V1,
            "asset0": self.asset0,
            "asset1": self.asset1,
            "fee_bps": self.fee_bps,
            "curve_kind": self.curve_kind,
            "curve_release_id": self.curve_release_id,
            "curve_params_root": self.curve_params_root,
        }


@dataclass(frozen=True, slots=True)
class ZDEXSpotPoolV1:
    pool_id: str
    definition: ZDEXSpotPoolDefinitionV1
    reserve0_atoms: int
    reserve1_atoms: int
    lp_supply_atoms: int
    status: ZDEXSpotPoolStatusV1
    creation_release_id: str
    created_height: int

    def __post_init__(self) -> None:
        _require_root(self.pool_id, name="Spot pool id")
        if type(self.definition) is not ZDEXSpotPoolDefinitionV1:
            raise TypeError("Spot pool definition must be exact typed data")
        for name in ("reserve0_atoms", "reserve1_atoms", "lp_supply_atoms"):
            _require_atoms_u128(getattr(self, name), name=f"Spot pool {name}")
        if type(self.status) is not ZDEXSpotPoolStatusV1:
            raise TypeError("Spot pool status is not closed")
        _require_root(self.creation_release_id, name="Spot pool creation release")
        _require_nonnegative_int(self.created_height, name="Spot pool created height")

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ZDEX_SPOT_POOL_SCHEMA_V1,
            "pool_id": self.pool_id,
            "definition": self.definition,
            "reserve0_atoms": self.reserve0_atoms,
            "reserve1_atoms": self.reserve1_atoms,
            "lp_supply_atoms": self.lp_supply_atoms,
            "status": self.status,
            "creation_release_id": self.creation_release_id,
            "created_height": self.created_height,
        }


@dataclass(frozen=True, slots=True)
class ZDEXSpotLaneStateV1:
    pools: tuple[ZDEXSpotPoolV1, ...]
    lp_ownership_root: str
    route_batch_root: str
    fee_residue_root: str
    pool_terminal_obligations_root: str

    def __post_init__(self) -> None:
        if type(self.pools) is not tuple or any(
            type(pool) is not ZDEXSpotPoolV1 for pool in self.pools
        ):
            raise TypeError("Spot lane pools must be an exact tuple")
        for name in (
            "lp_ownership_root",
            "route_batch_root",
            "fee_residue_root",
            "pool_terminal_obligations_root",
        ):
            _require_root(getattr(self, name), name=f"Spot lane {name}")

    @property
    def state_root(self) -> str:
        return hash_global_v1("zdex-spot-lane-state-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ZDEX_SPOT_LANE_STATE_SCHEMA_V1,
            "pools": self.pools,
            "lp_ownership_root": self.lp_ownership_root,
            "route_batch_root": self.route_batch_root,
            "fee_residue_root": self.fee_residue_root,
            "pool_terminal_obligations_root": self.pool_terminal_obligations_root,
        }


@dataclass(frozen=True, slots=True)
class ZDEXSpotProfileAuthorizationV1:
    profile_root: str
    chain_id: str
    deployment_root: str
    route_release_id: str
    spot_module_release_id: str
    tokenomics_module_release_id: str
    oracle_id: str
    release_root: str
    execution_policy_root: str
    price_policy_root: str

    def __post_init__(self) -> None:
        _require_token(self.chain_id, name="Spot profile chain id")
        _require_token(self.oracle_id, name="Spot profile Oracle id")
        for name in (
            "profile_root",
            "deployment_root",
            "route_release_id",
            "spot_module_release_id",
            "tokenomics_module_release_id",
            "release_root",
            "execution_policy_root",
            "price_policy_root",
        ):
            _require_root(getattr(self, name), name=f"Spot profile {name}")

    @property
    def authorization_root(self) -> str:
        return hash_global_v1(
            "zdex-spot-buyback-profile-authorization-v1",
            self.to_canonical(),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ZDEX_SPOT_PROFILE_AUTHORIZATION_SCHEMA_V1,
            "profile_root": self.profile_root,
            "chain_id": self.chain_id,
            "deployment_root": self.deployment_root,
            "route_release_id": self.route_release_id,
            "spot_module_release_id": self.spot_module_release_id,
            "tokenomics_module_release_id": self.tokenomics_module_release_id,
            "oracle_id": self.oracle_id,
            "release_root": self.release_root,
            "execution_policy_root": self.execution_policy_root,
            "price_policy_root": self.price_policy_root,
        }


@dataclass(frozen=True, slots=True)
class ZDEXSpotOracleOccurrenceV1:
    price: ZDEXBuybackOraclePriceOccurrenceV1
    finality_root: str
    status: ZDEXSpotOracleStatusV1

    def __post_init__(self) -> None:
        if type(self.price) is not ZDEXBuybackOraclePriceOccurrenceV1:
            raise TypeError("Spot Oracle price must be exact typed data")
        _require_root(self.finality_root, name="Spot Oracle finality root")
        if type(self.status) is not ZDEXSpotOracleStatusV1:
            raise TypeError("Spot Oracle status is not closed")

    @property
    def occurrence_id(self) -> str:
        return hash_global_v1("zdex-spot-oracle-occurrence-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "price": self.price,
            "finality_root": self.finality_root,
            "status": self.status,
        }


@dataclass(frozen=True, slots=True)
class ZDEXSpotOracleRegistryV1:
    occurrences: tuple[ZDEXSpotOracleOccurrenceV1, ...]

    def __post_init__(self) -> None:
        if type(self.occurrences) is not tuple or any(
            type(item) is not ZDEXSpotOracleOccurrenceV1 for item in self.occurrences
        ):
            raise TypeError("Spot Oracle registry must be an exact tuple")

    @property
    def registry_root(self) -> str:
        return hash_global_v1("zdex-spot-oracle-registry-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ZDEX_SPOT_ORACLE_REGISTRY_SCHEMA_V1,
            "occurrences": self.occurrences,
        }


@dataclass(frozen=True, slots=True)
class ZDEXSpotBuybackAuthorityContextV1:
    chain_id: str
    deployment_root: str
    profile_root: str
    profile_authorization_root: str
    route_release_id: str
    command_occurrence_id: str
    global_pre_state_root: str
    spot_pre_state_root: str
    writer_epoch: int
    current_height: int
    spot_module_release_id: str
    tokenomics_module_release_id: str
    release: ZDEXSpotBuybackReleaseV1
    execution_policy: ZDEXBuybackExecutionPolicyV1
    expected_pool_definition: ZDEXSpotPoolDefinitionV1
    price_policy: ZDEXBuybackPriceSafetyPolicyV1
    profile_authorization: ZDEXSpotProfileAuthorizationV1
    oracle_registry: ZDEXSpotOracleRegistryV1
    oracle_occurrence: ZDEXSpotOracleOccurrenceV1

    def __post_init__(self) -> None:
        _require_token(self.chain_id, name="Spot authority chain id")
        for name in (
            "deployment_root",
            "profile_root",
            "profile_authorization_root",
            "route_release_id",
            "command_occurrence_id",
            "global_pre_state_root",
            "spot_pre_state_root",
            "spot_module_release_id",
            "tokenomics_module_release_id",
        ):
            _require_root(getattr(self, name), name=f"Spot authority {name}")
        _require_nonnegative_int(self.writer_epoch, name="Spot authority writer epoch")
        _require_nonnegative_int(self.current_height, name="Spot authority current height")
        expected = (
            (self.release, ZDEXSpotBuybackReleaseV1),
            (self.execution_policy, ZDEXBuybackExecutionPolicyV1),
            (self.expected_pool_definition, ZDEXSpotPoolDefinitionV1),
            (self.price_policy, ZDEXBuybackPriceSafetyPolicyV1),
            (self.profile_authorization, ZDEXSpotProfileAuthorizationV1),
            (self.oracle_registry, ZDEXSpotOracleRegistryV1),
            (self.oracle_occurrence, ZDEXSpotOracleOccurrenceV1),
        )
        if any(type(value) is not kind for value, kind in expected):
            raise TypeError("Spot authority nested values must be exact typed data")


@dataclass(frozen=True, slots=True)
class ZDEXSpotQuoteInputPortV1:
    profile_root: str
    route_release_id: str
    command_occurrence_id: str
    global_pre_state_root: str
    spot_pre_state_root: str
    source_module_release_id: str
    destination_module_release_id: str
    source_pre_state_root: str
    source_post_state_root: str
    source_effect_plan_root: str
    source_journal_root: str
    source_receipt_binding_root: str
    amount_atoms: int

    def __post_init__(self) -> None:
        for name in (
            "profile_root",
            "route_release_id",
            "command_occurrence_id",
            "global_pre_state_root",
            "spot_pre_state_root",
            "source_module_release_id",
            "destination_module_release_id",
            "source_pre_state_root",
            "source_post_state_root",
            "source_effect_plan_root",
            "source_journal_root",
            "source_receipt_binding_root",
        ):
            _require_root(getattr(self, name), name=f"Spot quote port {name}")
        _require_atoms_u128(self.amount_atoms, name="Spot quote port amount")

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ZDEX_SPOT_QUOTE_INPUT_SCHEMA_V1,
            "profile_root": self.profile_root,
            "route_release_id": self.route_release_id,
            "command_occurrence_id": self.command_occurrence_id,
            "global_pre_state_root": self.global_pre_state_root,
            "spot_pre_state_root": self.spot_pre_state_root,
            "source_module_release_id": self.source_module_release_id,
            "destination_module_release_id": self.destination_module_release_id,
            "source_pre_state_root": self.source_pre_state_root,
            "source_post_state_root": self.source_post_state_root,
            "source_effect_plan_root": self.source_effect_plan_root,
            "source_journal_root": self.source_journal_root,
            "source_receipt_binding_root": self.source_receipt_binding_root,
            "amount_atoms": self.amount_atoms,
        }


@dataclass(frozen=True, slots=True)
class ZDEXSpotPriceEnvelopeV1:
    profile_root: str
    route_release_id: str
    command_occurrence_id: str
    global_pre_state_root: str
    spot_pre_state_root: str
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
        for name in (
            "profile_root",
            "route_release_id",
            "command_occurrence_id",
            "global_pre_state_root",
            "spot_pre_state_root",
            "selected_pool_id",
            "oracle_occurrence_id",
            "oracle_finality_root",
        ):
            _require_root(getattr(self, name), name=f"Spot price envelope {name}")
        for name in (
            "quote_amount_atoms",
            "oracle_quote_numerator_atoms",
            "oracle_zdex_denominator_atoms",
            "claimed_route_safe_quote_limit_atoms",
            "minimum_output_atoms",
        ):
            _require_atoms_u128(getattr(self, name), name=f"Spot price envelope {name}")
        _require_nonnegative_int(self.current_height, name="Spot price current height")
        _require_nonnegative_int(
            self.oracle_observed_height,
            name="Spot price Oracle observed height",
        )


@dataclass(frozen=True, slots=True)
class ZDEXSpotBuybackInputV1:
    authority: object
    pre_state: ZDEXSpotLaneStateV1
    quote_port: ZDEXSpotQuoteInputPortV1
    price_envelope: ZDEXSpotPriceEnvelopeV1

    def __post_init__(self) -> None:
        expected = (
            (self.pre_state, ZDEXSpotLaneStateV1),
            (self.quote_port, ZDEXSpotQuoteInputPortV1),
            (self.price_envelope, ZDEXSpotPriceEnvelopeV1),
        )
        if any(type(value) is not kind for value, kind in expected):
            raise TypeError("Spot buyback input requires exact typed values")


@dataclass(frozen=True, slots=True)
class ZDEXSpotFlowIdentityV1:
    role: ZDEXSpotFlowRoleV1
    context_root: str
    selected_pool_id: str
    asset: str
    source_principal: str
    destination_principal: str
    amount_atoms: int

    def __post_init__(self) -> None:
        if type(self.role) is not ZDEXSpotFlowRoleV1:
            raise TypeError("Spot flow role is not closed")
        for name in ("context_root", "selected_pool_id", "asset"):
            _require_root(getattr(self, name), name=f"Spot flow {name}")
        for name in ("source_principal", "destination_principal"):
            _require_token(getattr(self, name), name=f"Spot flow {name}")
        amount = _require_atoms_u128(self.amount_atoms, name="Spot flow amount")
        if amount == 0 or amount > MAX_DELTA_ATOMS_V1:
            raise ValueError("Spot flow amount must fit a positive signed effect")

    @property
    def flow_id(self) -> str:
        return hash_global_v1("zdex-spot-buyback-flow-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ZDEX_SPOT_FLOW_SCHEMA_V1,
            "role": self.role,
            "context_root": self.context_root,
            "selected_pool_id": self.selected_pool_id,
            "asset": self.asset,
            "source_principal": self.source_principal,
            "destination_principal": self.destination_principal,
            "amount_atoms": self.amount_atoms,
        }


@dataclass(frozen=True, slots=True)
class ZDEXSpotPrivatePortsV1:
    quote_input: ZDEXSpotFlowIdentityV1
    purchased_output: ZDEXSpotFlowIdentityV1

    def __post_init__(self) -> None:
        if (
            type(self.quote_input) is not ZDEXSpotFlowIdentityV1
            or type(self.purchased_output) is not ZDEXSpotFlowIdentityV1
            or self.quote_input.role is not ZDEXSpotFlowRoleV1.QUOTE_INPUT
            or self.purchased_output.role is not ZDEXSpotFlowRoleV1.PURCHASED_ZDEX_OUTPUT
            or self.quote_input.context_root != self.purchased_output.context_root
            or self.quote_input.selected_pool_id != self.purchased_output.selected_pool_id
        ):
            raise ValueError("Spot private ports do not form one exact role pair")

    @property
    def ports_root(self) -> str:
        return hash_global_v1(
            "zdex-spot-private-ports-v1",
            {
                "schema": ZDEX_SPOT_PRIVATE_PORTS_SCHEMA_V1,
                "quote_input": self.quote_input,
                "purchased_output": self.purchased_output,
                "quote_input_flow_id": self.quote_input.flow_id,
                "purchased_output_flow_id": self.purchased_output.flow_id,
            },
        )


@dataclass(frozen=True, slots=True)
class ZDEXSpotTerminalObligationV1:
    context_root: str
    post_state_root: str
    consumer_module_release_id: str
    burn_asset: str
    burn_principal: str
    selected_pool_id: str
    quote_input_flow_id: str
    purchased_output_flow_id: str
    purchased_atoms: int

    def __post_init__(self) -> None:
        for name in (
            "context_root",
            "post_state_root",
            "consumer_module_release_id",
            "burn_asset",
            "selected_pool_id",
            "quote_input_flow_id",
            "purchased_output_flow_id",
        ):
            _require_root(getattr(self, name), name=f"Spot terminal {name}")
        _require_token(self.burn_principal, name="Spot terminal burn principal")
        amount = _require_atoms_u128(self.purchased_atoms, name="Spot terminal amount")
        if amount == 0 or amount > MAX_DELTA_ATOMS_V1:
            raise ValueError("Spot terminal amount must fit a positive signed effect")

    @property
    def obligation_id(self) -> str:
        return hash_global_v1("zdex-spot-terminal-obligation-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ZDEX_SPOT_TERMINAL_OBLIGATION_SCHEMA_V1,
            "kind": "MUST_BURN_PURCHASED_ZDEX",
            "burn_domain": "ZDEX_TOKEN_SUPPLY",
            "context_root": self.context_root,
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
class ZDEXSpotBuybackJournalV1:
    context_root: str
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
        for name in (
            "context_root",
            "post_state_root",
            "effect_plan_root",
            "private_ports_root",
            "terminal_obligation_id",
            "selected_pool_id",
            "pool_definition_root",
        ):
            _require_root(getattr(self, name), name=f"Spot journal {name}")
        for name in (
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
            _require_atoms_u128(getattr(self, name), name=f"Spot journal {name}")
        if (
            self.quote_input_atoms == 0
            or self.purchased_zdex_atoms == 0
            or self.quote_input_atoms != self.fee_atoms + self.net_input_atoms
            or self.post_quote_reserve_atoms
            != self.pre_quote_reserve_atoms + self.quote_input_atoms
            or self.post_zdex_reserve_atoms + self.purchased_zdex_atoms
            != self.pre_zdex_reserve_atoms
        ):
            raise ValueError("Spot journal accounting projection is inconsistent")

    @property
    def journal_root(self) -> str:
        return hash_global_v1(
            "zdex-spot-buyback-transition-journal-v1",
            {
                "schema": ZDEX_SPOT_TRANSITION_JOURNAL_SCHEMA_V1,
                "context_root": self.context_root,
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
            },
        )


@dataclass(frozen=True, slots=True)
class ZDEXSpotBuybackRejectedV1:
    code: ZDEXSpotBuybackRejectCodeV1
    pre_state: ZDEXSpotLaneStateV1
    post_state: ZDEXSpotLaneStateV1
    effects: GlobalEconomicEffectPlanV1 = GlobalEconomicEffectPlanV1.empty()
    ports: None = None
    journal: None = None
    terminal_obligation: None = None

    def __post_init__(self) -> None:
        if type(self.code) is not ZDEXSpotBuybackRejectCodeV1:
            raise TypeError("Spot buyback reject code is not closed")
        if self.pre_state is not self.post_state or not self.effects.is_empty:
            raise ValueError("Spot buyback rejection must be an exact no-effect no-op")


@dataclass(frozen=True, slots=True)
class _ZDEXSpotBuybackAcceptedFieldsV1:
    pre_state: ZDEXSpotLaneStateV1
    post_state: ZDEXSpotLaneStateV1
    effects: GlobalEconomicEffectPlanV1
    ports: ZDEXSpotPrivatePortsV1
    journal: ZDEXSpotBuybackJournalV1
    terminal_obligation: ZDEXSpotTerminalObligationV1
    price_safety: VerifiedZDEXBuybackPriceSafetyV1


_ACCEPTED_GRAPH_LEAF_TYPES_V1: Final = frozenset(
    {
        str,
        int,
        bool,
        type(None),
        EconomicEffectKindV1,
        LaneIdV1,
        ReleaseStatusV1,
        ZDEXSpotPoolStatusV1,
        ZDEXSpotCurveKindV1,
        ZDEXSpotOracleStatusV1,
        ZDEXSpotFlowRoleV1,
    }
)

_ACCEPTED_GRAPH_DATACLASS_TYPES_V1: Final = frozenset(
    {
        AssetConservationRowV1,
        EconomicEffectRowV1,
        ExternalOutboxEnqueueV1,
        FeeConservationRowV1,
        GlobalEconomicEffectPlanV1,
        LaneWriteV1,
        ZDEXBuybackExecutionPolicyV1,
        ZDEXBuybackOraclePriceOccurrenceV1,
        ZDEXBuybackPriceSafetyObservationV1,
        ZDEXBuybackPriceSafetyPolicyV1,
        _VerifiedZDEXBuybackPriceSafetyFieldsV1,
        ZDEXSpotRegisteredCurveReleaseV1,
        ZDEXSpotPoolCreationReleaseV1,
        ZDEXSpotBuybackReleaseV1,
        ZDEXSpotPoolDefinitionV1,
        ZDEXSpotPoolV1,
        ZDEXSpotLaneStateV1,
        ZDEXSpotProfileAuthorizationV1,
        ZDEXSpotOracleOccurrenceV1,
        ZDEXSpotOracleRegistryV1,
        ZDEXSpotBuybackAuthorityContextV1,
        ZDEXSpotQuoteInputPortV1,
        ZDEXSpotPriceEnvelopeV1,
        ZDEXSpotBuybackInputV1,
        ZDEXSpotFlowIdentityV1,
        ZDEXSpotPrivatePortsV1,
        ZDEXSpotTerminalObligationV1,
        ZDEXSpotBuybackJournalV1,
        _ZDEXSpotBuybackAcceptedFieldsV1,
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
            raise ValueError("Spot buyback accepted graph exceeds node budget")
        if depth > _ACCEPTED_GRAPH_DEPTH_CAP_V1:
            raise ValueError("Spot buyback accepted graph exceeds depth budget")

        node_type = type(node)
        if node_type in _ACCEPTED_GRAPH_LEAF_TYPES_V1:
            return

        node_id = id(node)
        if node_id in active_ids:
            raise ValueError("Spot buyback accepted graph contains a cycle")
        active_ids.add(node_id)
        try:
            if node_type is tuple:
                for item in cast(tuple[object, ...], node):
                    visit(item, depth + 1)
                return
            if node_type is VerifiedZDEXBuybackPriceSafetyV1:
                inner = object.__getattribute__(node, "_fields")
                if type(inner) is not _VerifiedZDEXBuybackPriceSafetyFieldsV1:
                    raise TypeError("Spot buyback accepted price witness is not closed")
                visit(inner, depth + 1)
                return
            if node_type not in _ACCEPTED_GRAPH_DATACLASS_TYPES_V1:
                raise TypeError("Spot buyback accepted owned graph is not closed")
            dataclass_type = cast(type[_ZDEXSpotBuybackAcceptedFieldsV1], node_type)
            for field in dataclass_fields(dataclass_type):
                visit(object.__getattribute__(node, field.name), depth + 1)
        finally:
            active_ids.remove(node_id)

    visit(value, 0)


def _exact_accepted_graph_matches_v1(expected: object, supplied: object) -> bool:
    """Compare closed graphs without Python's cross-type equality aliases."""

    if type(expected) is not type(supplied):
        return False
    value_type = type(expected)
    if value_type is type(None):
        return True
    if value_type in {
        EconomicEffectKindV1,
        LaneIdV1,
        ReleaseStatusV1,
        ZDEXSpotPoolStatusV1,
        ZDEXSpotCurveKindV1,
        ZDEXSpotOracleStatusV1,
        ZDEXSpotFlowRoleV1,
    }:
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
    if value_type is VerifiedZDEXBuybackPriceSafetyV1:
        return _exact_accepted_graph_matches_v1(
            object.__getattribute__(expected, "_fields"),
            object.__getattribute__(supplied, "_fields"),
        )
    if value_type not in _ACCEPTED_GRAPH_DATACLASS_TYPES_V1:
        return False
    dataclass_type = cast(type[_ZDEXSpotBuybackAcceptedFieldsV1], value_type)
    return all(
        _exact_accepted_graph_matches_v1(
            object.__getattribute__(expected, field.name),
            object.__getattribute__(supplied, field.name),
        )
        for field in dataclass_fields(dataclass_type)
    )


def _require_accepted_projection_types_v1(
    subject: object,
    fields: object,
) -> tuple[ZDEXSpotBuybackInputV1, _ZDEXSpotBuybackAcceptedFieldsV1]:
    if type(subject) is not ZDEXSpotBuybackInputV1:
        raise TypeError("Spot buyback accepted subject is not closed")
    if type(fields) is not _ZDEXSpotBuybackAcceptedFieldsV1:
        raise TypeError("Spot buyback accepted fields are not closed")
    _require_exact_accepted_graph_v1(subject)
    _require_exact_accepted_graph_v1(fields)
    return subject, fields


def _accepted_fields_match(
    left: _ZDEXSpotBuybackAcceptedFieldsV1,
    right: _ZDEXSpotBuybackAcceptedFieldsV1,
) -> bool:
    return _exact_accepted_graph_matches_v1(left, right)


class ZDEXSpotBuybackAcceptedV1:
    """Revalidated SHADOW result; it is data rather than publication authority."""

    _subject: ZDEXSpotBuybackInputV1
    _fields: _ZDEXSpotBuybackAcceptedFieldsV1
    __slots__ = ("_subject", "_fields")

    def __init__(
        self,
        token: object,
        subject: ZDEXSpotBuybackInputV1,
        fields: _ZDEXSpotBuybackAcceptedFieldsV1,
    ) -> None:
        if token is not _ACCEPTED_TOKEN_V1:
            raise TypeError("Spot buyback accepted result requires local rederivation")
        subject, fields = _require_accepted_projection_types_v1(subject, fields)
        expected = _derive_zdex_spot_buyback_v1(subject)
        if type(expected) is not _ZDEXSpotBuybackAcceptedFieldsV1 or not _accepted_fields_match(
            expected,
            fields,
        ):
            raise ValueError("Spot buyback accepted projection does not rederive")
        object.__setattr__(self, "_subject", subject)
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("Spot buyback accepted result is immutable")

    @property
    def pre_state(self) -> ZDEXSpotLaneStateV1:
        return self._fields.pre_state

    @property
    def post_state(self) -> ZDEXSpotLaneStateV1:
        return self._fields.post_state

    @property
    def effects(self) -> GlobalEconomicEffectPlanV1:
        return self._fields.effects

    @property
    def ports(self) -> ZDEXSpotPrivatePortsV1:
        return self._fields.ports

    @property
    def journal(self) -> ZDEXSpotBuybackJournalV1:
        return self._fields.journal

    @property
    def terminal_obligation(self) -> ZDEXSpotTerminalObligationV1:
        return self._fields.terminal_obligation

    @property
    def price_safety(self) -> VerifiedZDEXBuybackPriceSafetyV1:
        return self._fields.price_safety

    def validate(self) -> None:
        subject, fields = _require_accepted_projection_types_v1(
            object.__getattribute__(self, "_subject"),
            object.__getattribute__(self, "_fields"),
        )
        expected = _derive_zdex_spot_buyback_v1(subject)
        if type(expected) is not _ZDEXSpotBuybackAcceptedFieldsV1 or not _accepted_fields_match(
            expected,
            fields,
        ):
            raise ValueError("Spot buyback accepted projection no longer rederives")


ZDEXSpotBuybackResultV1: TypeAlias = ZDEXSpotBuybackAcceptedV1 | ZDEXSpotBuybackRejectedV1


@dataclass(frozen=True, slots=True)
class _ZDEXSpotSwapAmountsV1:
    gross: int
    fee: int
    net: int
    purchased: int


@dataclass(frozen=True, slots=True)
class _ZDEXSpotSelectedPoolV1:
    index: int
    pool: ZDEXSpotPoolV1


def _reject(
    code: ZDEXSpotBuybackRejectCodeV1,
    state: ZDEXSpotLaneStateV1,
) -> ZDEXSpotBuybackRejectedV1:
    return ZDEXSpotBuybackRejectedV1(code, state, state)


def _checked_product(*values: int) -> int | None:
    product = 1
    for value in values:
        if value and product > MAX_ATOMS_V1 // value:
            return None
        product *= value
    return product


def _fee_atoms(gross: int, fee_bps: int) -> int | None:
    product = _checked_product(gross, fee_bps)
    if product is None or product > MAX_ATOMS_V1 - (BASIS_POINTS_V1 - 1):
        return None
    return (product + BASIS_POINTS_V1 - 1) // BASIS_POINTS_V1


def _pool_static_well_formed(
    release: ZDEXSpotBuybackReleaseV1,
    pool: ZDEXSpotPoolV1,
) -> bool:
    definition = pool.definition
    if (
        pool.pool_id != definition.pool_id
        or not definition.asset0 < definition.asset1
        or definition.fee_bps > BASIS_POINTS_V1
        or not any(
            row.module_release_id == pool.creation_release_id
            and row.status in {ReleaseStatusV1.ACTIVE_NEW, ReleaseStatusV1.DRAIN_ONLY}
            for row in release.pool_creation_releases
        )
    ):
        return False
    if definition.curve_kind is ZDEXSpotCurveKindV1.CPMM_V8_EXACT_IN:
        return (
            definition.curve_release_id == release.cpmm_curve_release_id
            and definition.curve_params_root == ZERO_ROOT_V1
        )
    return definition.curve_params_root != ZERO_ROOT_V1 and any(
        row.release_id == definition.curve_release_id
        and row.status in {ReleaseStatusV1.ACTIVE_NEW, ReleaseStatusV1.DRAIN_ONLY}
        for row in release.registered_sibling_curve_releases
    )


def _pool_well_formed(release: ZDEXSpotBuybackReleaseV1, pool: ZDEXSpotPoolV1) -> bool:
    bounded = all(
        value <= release.reserve_cap_atoms
        for value in (pool.reserve0_atoms, pool.reserve1_atoms, pool.lp_supply_atoms)
    )
    active_positive = pool.status is not ZDEXSpotPoolStatusV1.ACTIVE or all(
        value > 0 for value in (pool.reserve0_atoms, pool.reserve1_atoms, pool.lp_supply_atoms)
    )
    return _pool_static_well_formed(release, pool) and bounded and active_positive


def _lane_well_formed(
    release: ZDEXSpotBuybackReleaseV1,
    state: ZDEXSpotLaneStateV1,
) -> bool:
    ids = tuple(pool.pool_id for pool in state.pools)
    return (
        0 < len(state.pools) <= release.pool_count_cap
        and ids == tuple(sorted(set(ids)))
        and all(_pool_well_formed(release, pool) for pool in state.pools)
    )


def _price_arithmetic_fits(
    authority: ZDEXSpotBuybackAuthorityContextV1,
    pool: ZDEXSpotPoolV1,
    amounts: _ZDEXSpotSwapAmountsV1,
    envelope: ZDEXSpotPriceEnvelopeV1,
) -> bool:
    policy = authority.price_policy
    gross = amounts.gross
    fee = amounts.fee
    net = amounts.net
    purchased = amounts.purchased
    oracle_observed_height = authority.oracle_occurrence.price.observed_height
    pool_oracle_quote = _checked_product(
        pool.reserve0_atoms,
        envelope.oracle_zdex_denominator_atoms,
    )
    pool_oracle_zdex = _checked_product(
        pool.reserve1_atoms,
        envelope.oracle_quote_numerator_atoms,
    )
    pool_oracle_difference = (
        None
        if pool_oracle_quote is None or pool_oracle_zdex is None
        else abs(pool_oracle_quote - pool_oracle_zdex)
    )
    if authority.writer_epoch > MAX_U64_V1 or authority.current_height > MAX_U64_V1:
        return False
    execution_products = (
        _checked_product(gross, pool.definition.fee_bps),
        _checked_product(pool.reserve1_atoms, net),
        _checked_product(pool.reserve0_atoms, policy.maximum_quote_reserve_spend_bps),
        _checked_product(gross, envelope.oracle_zdex_denominator_atoms),
        _checked_product(gross, envelope.oracle_zdex_denominator_atoms, BASIS_POINTS_V1),
        _checked_product(
            envelope.oracle_quote_numerator_atoms,
            BASIS_POINTS_V1 + policy.maximum_oracle_execution_deviation_bps,
        ),
        _checked_product(
            gross,
            pool.reserve1_atoms,
            BASIS_POINTS_V1,
        ),
        _checked_product(
            purchased,
            pool.reserve0_atoms,
            BASIS_POINTS_V1 + policy.maximum_execution_impact_bps,
        ),
        _checked_product(
            purchased,
            envelope.oracle_quote_numerator_atoms,
            BASIS_POINTS_V1 + policy.maximum_oracle_execution_deviation_bps,
        ),
    )
    pool_oracle_products = (
        pool_oracle_quote,
        pool_oracle_zdex,
        None
        if pool_oracle_difference is None
        else _checked_product(pool_oracle_difference, BASIS_POINTS_V1),
        _checked_product(
            pool.reserve1_atoms,
            envelope.oracle_quote_numerator_atoms,
            policy.maximum_pool_oracle_deviation_bps,
        ),
    )
    return (
        oracle_observed_height <= MAX_U64_V1
        and fee <= MAX_ATOMS_V1
        and net <= MAX_ATOMS_V1
        and pool.reserve0_atoms <= MAX_ATOMS_V1 - net
        and gross <= MAX_DELTA_ATOMS_V1
        and purchased <= MAX_DELTA_ATOMS_V1
        and all(value is not None for value in (*execution_products, *pool_oracle_products))
    )


def _context_root(
    authority: ZDEXSpotBuybackAuthorityContextV1,
    quote_port: ZDEXSpotQuoteInputPortV1,
) -> str:
    return hash_global_v1(
        "zdex-spot-buyback-transition-context-v1",
        {
            "chain_id": authority.chain_id,
            "deployment_root": authority.deployment_root,
            "profile_root": authority.profile_root,
            "profile_authorization_root": authority.profile_authorization_root,
            "route_release_id": authority.route_release_id,
            "command_occurrence_id": authority.command_occurrence_id,
            "global_pre_state_root": authority.global_pre_state_root,
            "spot_pre_state_root": authority.spot_pre_state_root,
            "writer_epoch": authority.writer_epoch,
            "current_height": authority.current_height,
            "spot_module_release_id": authority.spot_module_release_id,
            "tokenomics_module_release_id": authority.tokenomics_module_release_id,
            "release_root": authority.release.release_root,
            "execution_policy_root": authority.execution_policy.policy_root,
            "price_policy_root": authority.price_policy.policy_root,
            "oracle_registry_root": authority.oracle_registry.registry_root,
            "oracle_occurrence_id": authority.oracle_occurrence.occurrence_id,
            "tokenomics_source_pre_state_root": quote_port.source_pre_state_root,
            "tokenomics_source_post_state_root": quote_port.source_post_state_root,
            "tokenomics_source_effect_plan_root": quote_port.source_effect_plan_root,
            "tokenomics_source_journal_root": quote_port.source_journal_root,
            "tokenomics_source_receipt_binding_root": quote_port.source_receipt_binding_root,
        },
    )


def _release_matches_v1(authority: ZDEXSpotBuybackAuthorityContextV1) -> bool:
    release = authority.release
    return (
        release.is_bounded_v1
        and authority.route_release_id == release.route_release_id
        and authority.spot_module_release_id == release.spot_module_release_id
        and authority.tokenomics_module_release_id == release.tokenomics_module_release_id
    )


def _profile_matches_v1(authority: ZDEXSpotBuybackAuthorityContextV1) -> bool:
    profile = authority.profile_authorization
    return (
        authority.profile_authorization_root == profile.authorization_root
        and profile.profile_root == authority.profile_root
        and profile.chain_id == authority.chain_id
        and profile.deployment_root == authority.deployment_root
        and profile.route_release_id == authority.route_release_id
        and profile.spot_module_release_id == authority.spot_module_release_id
        and profile.tokenomics_module_release_id == authority.tokenomics_module_release_id
        and profile.oracle_id == authority.price_policy.oracle_id
        and profile.release_root == authority.release.release_root
        and profile.execution_policy_root == authority.execution_policy.policy_root
        and profile.price_policy_root == authority.price_policy.policy_root
    )


def _quote_matches_v1(
    candidate: ZDEXSpotBuybackInputV1,
    authority: ZDEXSpotBuybackAuthorityContextV1,
) -> bool:
    quote = candidate.quote_port
    return (
        quote.profile_root == authority.profile_root
        and quote.route_release_id == authority.route_release_id
        and quote.command_occurrence_id == authority.command_occurrence_id
        and quote.global_pre_state_root == authority.global_pre_state_root
        and quote.spot_pre_state_root == authority.spot_pre_state_root
        and quote.source_module_release_id == authority.tokenomics_module_release_id
        and quote.destination_module_release_id == authority.spot_module_release_id
        and quote.source_pre_state_root != quote.source_post_state_root
    )


def _oracle_matches_v1(authority: ZDEXSpotBuybackAuthorityContextV1) -> bool:
    policy = authority.execution_policy
    price_policy = authority.price_policy
    oracle = authority.oracle_occurrence
    registry = authority.oracle_registry
    occurrence_ids = tuple(item.occurrence_id for item in registry.occurrences)
    return (
        bool(occurrence_ids)
        and occurrence_ids == tuple(sorted(set(occurrence_ids)))
        and registry.registry_root != ZERO_ROOT_V1
        and oracle in registry.occurrences
        and oracle.status is ZDEXSpotOracleStatusV1.FINAL
        and oracle.price.oracle_id == price_policy.oracle_id
        and oracle.price.quote_asset_id == policy.quote_asset_id
        and oracle.price.zdex_asset_id == policy.zdex_asset_id
        and all(
            item.status is ZDEXSpotOracleStatusV1.FINAL
            and item.price.oracle_id == price_policy.oracle_id
            for item in registry.occurrences
        )
    )


def _price_subject_matches_v1(
    candidate: ZDEXSpotBuybackInputV1,
    authority: ZDEXSpotBuybackAuthorityContextV1,
) -> bool:
    quote = candidate.quote_port
    envelope = candidate.price_envelope
    oracle = authority.oracle_occurrence
    return (
        envelope.profile_root == authority.profile_root
        and envelope.route_release_id == authority.route_release_id
        and envelope.command_occurrence_id == authority.command_occurrence_id
        and envelope.global_pre_state_root == authority.global_pre_state_root
        and envelope.spot_pre_state_root == authority.spot_pre_state_root
        and envelope.selected_pool_id == authority.execution_policy.pool_id
        and envelope.oracle_occurrence_id == oracle.occurrence_id
        and envelope.oracle_finality_root == oracle.finality_root
        and envelope.quote_amount_atoms == quote.amount_atoms
        and envelope.current_height == authority.current_height
        and envelope.oracle_observed_height == oracle.price.observed_height
        and envelope.oracle_quote_numerator_atoms == oracle.price.quote_numerator_atoms
        and envelope.oracle_zdex_denominator_atoms == oracle.price.zdex_denominator_atoms
    )


def _policy_matches_v1(authority: ZDEXSpotBuybackAuthorityContextV1) -> bool:
    policy = authority.execution_policy
    expected = authority.expected_pool_definition
    return (
        policy.pool_id == expected.pool_id
        and policy.pool_definition_root == expected.definition_root
        and expected.asset0 == policy.quote_asset_id
        and expected.asset1 == policy.zdex_asset_id
        and policy.quote_asset_id < policy.zdex_asset_id
        and expected.curve_kind is ZDEXSpotCurveKindV1.CPMM_V8_EXACT_IN
        and expected.curve_release_id == authority.release.cpmm_curve_release_id
        and expected.curve_params_root == ZERO_ROOT_V1
    )


def _select_pool_v1(
    candidate: ZDEXSpotBuybackInputV1,
    authority: ZDEXSpotBuybackAuthorityContextV1,
) -> _ZDEXSpotSelectedPoolV1 | ZDEXSpotBuybackRejectCodeV1:
    policy = authority.execution_policy
    selected_rows = tuple(
        (index, pool)
        for index, pool in enumerate(candidate.pre_state.pools)
        if pool.pool_id == policy.pool_id
    )
    if len(selected_rows) != 1:
        return ZDEXSpotBuybackRejectCodeV1.SELECTION_MISMATCH
    index, selected = selected_rows[0]
    if selected.definition != authority.expected_pool_definition:
        return ZDEXSpotBuybackRejectCodeV1.SELECTION_MISMATCH
    if selected.status is not ZDEXSpotPoolStatusV1.ACTIVE:
        return ZDEXSpotBuybackRejectCodeV1.POOL_INACTIVE
    return _ZDEXSpotSelectedPoolV1(index, selected)


def _derive_swap_amounts_v1(
    candidate: ZDEXSpotBuybackInputV1,
    authority: ZDEXSpotBuybackAuthorityContextV1,
    selected: ZDEXSpotPoolV1,
) -> _ZDEXSpotSwapAmountsV1 | ZDEXSpotBuybackRejectCodeV1:
    release = authority.release
    envelope = candidate.price_envelope
    gross = candidate.quote_port.amount_atoms
    if (
        gross == 0
        or gross > release.swap_cap_atoms
        or selected.reserve0_atoms > release.reserve_cap_atoms - gross
    ):
        return ZDEXSpotBuybackRejectCodeV1.AMOUNT_OUT_OF_RANGE
    fee = _fee_atoms(gross, selected.definition.fee_bps)
    if fee is None:
        return ZDEXSpotBuybackRejectCodeV1.ARITHMETIC_OUT_OF_RANGE
    net = gross - fee if fee <= gross else 0
    denominator = selected.reserve0_atoms + net
    output_product = _checked_product(selected.reserve1_atoms, net)
    purchased = 0 if output_product is None or denominator == 0 else output_product // denominator
    amounts = _ZDEXSpotSwapAmountsV1(gross, fee, net, purchased)
    if not _price_arithmetic_fits(authority, selected, amounts, envelope):
        return ZDEXSpotBuybackRejectCodeV1.ARITHMETIC_OUT_OF_RANGE
    if fee >= gross:
        return ZDEXSpotBuybackRejectCodeV1.FEE_CONSUMES_INPUT
    if purchased == 0:
        return ZDEXSpotBuybackRejectCodeV1.ZERO_OUTPUT
    if envelope.minimum_output_atoms == 0 or envelope.minimum_output_atoms > purchased:
        return ZDEXSpotBuybackRejectCodeV1.MINIMUM_OUTPUT_MISMATCH
    if envelope.claimed_route_safe_quote_limit_atoms == 0:
        return ZDEXSpotBuybackRejectCodeV1.PRICE_UNSAFE
    return amounts


def _verify_price_safety_v1(
    candidate: ZDEXSpotBuybackInputV1,
    authority: ZDEXSpotBuybackAuthorityContextV1,
    selected: ZDEXSpotPoolV1,
    amounts: _ZDEXSpotSwapAmountsV1,
) -> VerifiedZDEXBuybackPriceSafetyV1 | ZDEXSpotBuybackRejectCodeV1:
    envelope = candidate.price_envelope
    oracle = authority.oracle_occurrence
    observation = ZDEXBuybackPriceSafetyObservationV1(
        oracle_occurrence_root=oracle.price.occurrence_root,
        current_height=envelope.current_height,
        oracle_observed_height=envelope.oracle_observed_height,
        oracle_quote_numerator_atoms=envelope.oracle_quote_numerator_atoms,
        oracle_zdex_denominator_atoms=envelope.oracle_zdex_denominator_atoms,
        quote_reserve_atoms=selected.reserve0_atoms,
        zdex_reserve_atoms=selected.reserve1_atoms,
        quote_amount_in_atoms=amounts.gross,
        purchased_zdex_atoms=amounts.purchased,
        claimed_route_safe_quote_limit_atoms=envelope.claimed_route_safe_quote_limit_atoms,
        claimed_minimum_output_atoms=envelope.minimum_output_atoms,
    )
    result = verify_zdex_buyback_price_safety_v1(authority.price_policy, observation)
    if isinstance(result, ZDEXBuybackPriceSafetyRejectedV1):
        if result.code.value.startswith("DERIVED_MINIMUM_OUTPUT"):
            return ZDEXSpotBuybackRejectCodeV1.MINIMUM_OUTPUT_MISMATCH
        return ZDEXSpotBuybackRejectCodeV1.PRICE_UNSAFE
    if type(result) is not VerifiedZDEXBuybackPriceSafetyV1:
        return ZDEXSpotBuybackRejectCodeV1.PRICE_UNSAFE
    return result


def _build_post_state_v1(
    pre_state: ZDEXSpotLaneStateV1,
    selection: _ZDEXSpotSelectedPoolV1,
    amounts: _ZDEXSpotSwapAmountsV1,
) -> tuple[ZDEXSpotLaneStateV1, ZDEXSpotPoolV1]:
    selected = selection.pool
    updated = ZDEXSpotPoolV1(
        selected.pool_id,
        selected.definition,
        selected.reserve0_atoms + amounts.gross,
        selected.reserve1_atoms - amounts.purchased,
        selected.lp_supply_atoms,
        selected.status,
        selected.creation_release_id,
        selected.created_height,
    )
    pools = (*pre_state.pools[: selection.index], updated, *pre_state.pools[selection.index + 1 :])
    post_state = ZDEXSpotLaneStateV1(
        pools,
        pre_state.lp_ownership_root,
        pre_state.route_batch_root,
        pre_state.fee_residue_root,
        pre_state.pool_terminal_obligations_root,
    )
    return post_state, updated


def _build_effects_v1(
    pre_state: ZDEXSpotLaneStateV1,
    post_state: ZDEXSpotLaneStateV1,
    selected: ZDEXSpotPoolV1,
    authority: ZDEXSpotBuybackAuthorityContextV1,
    amounts: _ZDEXSpotSwapAmountsV1,
) -> tuple[GlobalEconomicEffectPlanV1, str, str]:
    policy = authority.execution_policy
    quote_pool = zdex_pool_reserve_principal_v1(
        pool_id=selected.pool_id,
        asset_id=policy.quote_asset_id,
    )
    zdex_pool = zdex_pool_reserve_principal_v1(
        pool_id=selected.pool_id,
        asset_id=policy.zdex_asset_id,
    )
    rows = tuple(
        sorted(
            (
                EconomicEffectRowV1(
                    EconomicEffectKindV1.ACCOUNT_MOVEMENT,
                    quote_pool,
                    policy.quote_asset_id,
                    AMM_POOL_CUSTODY_DOMAIN_V1,
                    amounts.gross,
                ),
                EconomicEffectRowV1(
                    EconomicEffectKindV1.ACCOUNT_MOVEMENT,
                    zdex_pool,
                    policy.zdex_asset_id,
                    AMM_POOL_CUSTODY_DOMAIN_V1,
                    -amounts.purchased,
                ),
            ),
            key=lambda row: row.key,
        )
    )
    effects = GlobalEconomicEffectPlanV1(
        rows=rows,
        asset_conservation=(),
        fee_conservation=(),
        lane_writes=(LaneWriteV1(LaneIdV1.SPOT_LIQUIDITY, pre_state.state_root, post_state.state_root),),
        occurrence_consumptions=(),
        external_outbox_enqueue=(),
    )
    return effects, quote_pool, zdex_pool


def _build_ports_and_terminal_v1(
    authority: ZDEXSpotBuybackAuthorityContextV1,
    selected: ZDEXSpotPoolV1,
    amounts: _ZDEXSpotSwapAmountsV1,
    post_state: ZDEXSpotLaneStateV1,
    quote_pool: str,
    zdex_pool: str,
    context_root: str,
) -> tuple[ZDEXSpotPrivatePortsV1, ZDEXSpotTerminalObligationV1]:
    policy = authority.execution_policy
    burn_principal = zdex_occurrence_burn_port_v1(
        profile_root=authority.profile_root,
        route_release_id=authority.route_release_id,
        command_occurrence_id=authority.command_occurrence_id,
    )
    quote_flow = ZDEXSpotFlowIdentityV1(
        ZDEXSpotFlowRoleV1.QUOTE_INPUT,
        context_root,
        selected.pool_id,
        policy.quote_asset_id,
        FEE_BUYBACK_PRINCIPAL_V1,
        quote_pool,
        amounts.gross,
    )
    purchased_flow = ZDEXSpotFlowIdentityV1(
        ZDEXSpotFlowRoleV1.PURCHASED_ZDEX_OUTPUT,
        context_root,
        selected.pool_id,
        policy.zdex_asset_id,
        zdex_pool,
        burn_principal,
        amounts.purchased,
    )
    ports = ZDEXSpotPrivatePortsV1(quote_flow, purchased_flow)
    terminal = ZDEXSpotTerminalObligationV1(
        context_root,
        post_state.state_root,
        authority.tokenomics_module_release_id,
        policy.zdex_asset_id,
        burn_principal,
        selected.pool_id,
        quote_flow.flow_id,
        purchased_flow.flow_id,
        amounts.purchased,
    )
    return ports, terminal


def _build_journal_v1(
    candidate: ZDEXSpotBuybackInputV1,
    selected: ZDEXSpotPoolV1,
    updated: ZDEXSpotPoolV1,
    amounts: _ZDEXSpotSwapAmountsV1,
    post_state: ZDEXSpotLaneStateV1,
    effects: GlobalEconomicEffectPlanV1,
    ports: ZDEXSpotPrivatePortsV1,
    terminal: ZDEXSpotTerminalObligationV1,
    context_root: str,
) -> ZDEXSpotBuybackJournalV1:
    envelope = candidate.price_envelope
    return ZDEXSpotBuybackJournalV1(
        context_root,
        post_state.state_root,
        effects.effect_plan_root,
        ports.ports_root,
        terminal.obligation_id,
        selected.pool_id,
        selected.definition.definition_root,
        amounts.gross,
        amounts.fee,
        amounts.net,
        amounts.purchased,
        envelope.claimed_route_safe_quote_limit_atoms,
        envelope.minimum_output_atoms,
        selected.reserve0_atoms,
        updated.reserve0_atoms,
        selected.reserve1_atoms,
        updated.reserve1_atoms,
    )


def _build_accepted_fields_v1(
    candidate: ZDEXSpotBuybackInputV1,
    authority: ZDEXSpotBuybackAuthorityContextV1,
    selection: _ZDEXSpotSelectedPoolV1,
    amounts: _ZDEXSpotSwapAmountsV1,
    price_safety: VerifiedZDEXBuybackPriceSafetyV1,
) -> _ZDEXSpotBuybackAcceptedFieldsV1:
    pre_state = candidate.pre_state
    selected = selection.pool
    post_state, updated = _build_post_state_v1(pre_state, selection, amounts)
    effects, quote_pool, zdex_pool = _build_effects_v1(
        pre_state, post_state, selected, authority, amounts
    )
    context_root = _context_root(authority, candidate.quote_port)
    ports, terminal = _build_ports_and_terminal_v1(
        authority,
        selected,
        amounts,
        post_state,
        quote_pool,
        zdex_pool,
        context_root,
    )
    journal = _build_journal_v1(
        candidate,
        selected,
        updated,
        amounts,
        post_state,
        effects,
        ports,
        terminal,
        context_root,
    )
    return _ZDEXSpotBuybackAcceptedFieldsV1(
        pre_state, post_state, effects, ports, journal, terminal, price_safety
    )


def _first_context_reject_v1(
    candidate: ZDEXSpotBuybackInputV1,
    authority: ZDEXSpotBuybackAuthorityContextV1,
) -> ZDEXSpotBuybackRejectCodeV1 | None:
    if not _release_matches_v1(authority):
        return ZDEXSpotBuybackRejectCodeV1.RELEASE_MISMATCH
    if not _profile_matches_v1(authority):
        return ZDEXSpotBuybackRejectCodeV1.PROFILE_MISMATCH
    if authority.spot_pre_state_root != candidate.pre_state.state_root:
        return ZDEXSpotBuybackRejectCodeV1.STATE_COMMITMENT_MISMATCH
    if not _quote_matches_v1(candidate, authority):
        return ZDEXSpotBuybackRejectCodeV1.QUOTE_PORT_MISMATCH
    if not _oracle_matches_v1(authority):
        return ZDEXSpotBuybackRejectCodeV1.ORACLE_MISMATCH
    if not _price_subject_matches_v1(candidate, authority):
        return ZDEXSpotBuybackRejectCodeV1.PRICE_SUBJECT_MISMATCH
    if not _policy_matches_v1(authority):
        return ZDEXSpotBuybackRejectCodeV1.POLICY_MISMATCH
    if not _lane_well_formed(authority.release, candidate.pre_state):
        return ZDEXSpotBuybackRejectCodeV1.LANE_MALFORMED
    return None


def _derive_zdex_spot_buyback_v1(
    candidate: ZDEXSpotBuybackInputV1,
) -> _ZDEXSpotBuybackAcceptedFieldsV1 | ZDEXSpotBuybackRejectedV1:
    """Run the ordered guards and derive fields without constructing authority."""

    if type(candidate) is not ZDEXSpotBuybackInputV1:
        raise TypeError("Spot buyback candidate must be exact typed data")
    pre_state = candidate.pre_state
    if type(candidate.authority) is not ZDEXSpotBuybackAuthorityContextV1:
        return _reject(ZDEXSpotBuybackRejectCodeV1.AUTHORITY_MALFORMED, pre_state)
    authority = candidate.authority
    context_reject = _first_context_reject_v1(candidate, authority)
    if context_reject is not None:
        return _reject(context_reject, pre_state)
    selection = _select_pool_v1(candidate, authority)
    if isinstance(selection, ZDEXSpotBuybackRejectCodeV1):
        return _reject(selection, pre_state)
    amounts = _derive_swap_amounts_v1(candidate, authority, selection.pool)
    if isinstance(amounts, ZDEXSpotBuybackRejectCodeV1):
        return _reject(amounts, pre_state)
    price_safety = _verify_price_safety_v1(candidate, authority, selection.pool, amounts)
    if isinstance(price_safety, ZDEXSpotBuybackRejectCodeV1):
        return _reject(price_safety, pre_state)
    return _build_accepted_fields_v1(candidate, authority, selection, amounts, price_safety)


def transition_zdex_spot_buyback_v1(
    candidate: ZDEXSpotBuybackInputV1,
) -> ZDEXSpotBuybackResultV1:
    """Return a revalidated SHADOW result or an exact typed no-op rejection."""

    derived = _derive_zdex_spot_buyback_v1(candidate)
    if type(derived) is ZDEXSpotBuybackRejectedV1:
        return derived
    if type(derived) is not _ZDEXSpotBuybackAcceptedFieldsV1:
        raise TypeError("Spot buyback derivation result is not closed")
    return ZDEXSpotBuybackAcceptedV1(_ACCEPTED_TOKEN_V1, candidate, derived)


__all__ = [name for name in globals() if name.startswith("ZDEX") or name.startswith("transition_")]
