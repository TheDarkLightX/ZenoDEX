"""Shadow receipt boundary for a governed ZDEX buyback Spot purchase.

This module authenticates one minimum-sufficient public journal under the Spot
image selected by a complete SHADOW economic profile.  It creates no route,
publishes no state, and grants no value-moving authority.  The callback is the
cryptographic authority for the exact ``(image_id, canonical_journal_bytes)``
claim; every host-side input is copied and revalidated before that callback.
"""

from __future__ import annotations

import hashlib
from copy import deepcopy
from dataclasses import dataclass, field, replace
from enum import Enum
from typing import Final, NoReturn

from .economic_receipt_verifier_deployment_v1 import BoundEconomicReceiptVerifierV1
from .economic_receipt_verifier_registry_v1 import (
    EconomicReceiptVerifierSelectionPurposeV1,
)
from .global_economic_authority_head_v1 import (
    GlobalEconomicAuthorityHeadV1,
    GlobalEconomicAuthorityStatusV1,
)
from .global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from .global_economic_proof_v1 import EconomicCommandOccurrenceV1, ReceiptKindV1
from .global_economic_refinement_snapshot_v1 import (
    _require_exact_dataclass_scalars_v1,
    _snapshot_occurrence_v1,
    _snapshot_state_v1,
)
from .global_settlement_types_v1 import (
    MAX_DELTA_ATOMS_V1,
    EconomicPolicyBindingV1,
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    GlobalEconomicStateV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    RouteReleaseV1,
    _require_atoms_u128,
    _require_nonnegative_int,
    _require_root,
    _require_token,
    canonical_global_bytes_v1,
    hash_global_v1,
)
from .zdex_atomic_buyback_state_v1 import ZDEXAtomicBuybackTokenomicsStateV1
from .zdex_buyback_price_safety_v1 import (
    ZDEX_BUYBACK_PRICE_SAFETY_POLICY_KIND_V1,
    VerifiedZDEXBuybackPriceSafetyV1,
    ZDEXBuybackPriceSafetyObservationV1,
    ZDEXBuybackPriceSafetyPolicyV1,
    ZDEXBuybackPriceSafetyRejectedV1,
    verify_zdex_buyback_price_safety_v1,
)
from .zdex_buyback_spend_v1 import (
    ZDEX_BUYBACK_SPEND_POLICY_KIND_V1,
    ZDEXBuybackSpendPolicyV1,
)
from .zdex_fee_allocation_receipt_verification_v1 import _snapshot_fee_policy_v1
from .zdex_fee_allocation_types_v1 import (
    ZDEX_FEE_ALLOCATION_POLICY_KIND_V1,
    ZDEXFeeAllocationCommandV1,
    ZDEXFeeAllocationContextV1,
    ZDEXFeeAllocationPolicyV1,
)
from .zdex_purchase_burn_route_types_v1 import (
    AMM_POOL_CUSTODY_DOMAIN_V1,
    AMM_PURCHASE_OUTPUT_ROLE_V1,
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    ZDEX_BURN_INPUT_ROLE_V1,
    ZDEX_BUYBACK_EXECUTION_POLICY_KIND_V1,
    ZDEXBuybackExecutionPolicyV1,
    zdex_amm_purchase_port_schema_root_v1,
    zdex_burn_port_schema_root_v1,
    zdex_pool_reserve_principal_v1,
)
from .zdex_verified_fee_ingress_slice_v1 import (
    VerifiedZDEXFeeIngressSliceV1,
    _derive_verified_zdex_fee_ingress_slice_v1,
)

ZDEX_BUYBACK_SPOT_SAFETY_PURCHASE_JOURNAL_SCHEMA_V1: Final = (
    "zenodex/zdex-buyback-spot-safety-purchase-journal/v1"
)
VERIFIED_ZDEX_BUYBACK_SPOT_SAFETY_PURCHASE_SCHEMA_V1: Final = (
    "zenodex/verified-zdex-buyback-spot-safety-purchase/v1"
)
_VERIFIED_ZDEX_BUYBACK_SPOT_TOKEN_V1 = object()


class ZDEXBuybackSpotReceiptRejectCodeV1(str, Enum):
    MALFORMED_CANDIDATE = "MALFORMED_CANDIDATE"
    AUTHORITY_BINDING_MISMATCH = "AUTHORITY_BINDING_MISMATCH"
    SHADOW_PROFILE_REQUIRED = "SHADOW_PROFILE_REQUIRED"
    GOVERNED_ROUTE_MISMATCH = "GOVERNED_ROUTE_MISMATCH"
    GOVERNED_SPOT_RELEASE_MISMATCH = "GOVERNED_SPOT_RELEASE_MISMATCH"
    GOVERNED_POLICY_MISMATCH = "GOVERNED_POLICY_MISMATCH"
    OCCURRENCE_BINDING_MISMATCH = "OCCURRENCE_BINDING_MISMATCH"
    STATE_ROOT_BINDING_MISMATCH = "STATE_ROOT_BINDING_MISMATCH"
    ORACLE_BINDING_MISMATCH = "ORACLE_BINDING_MISMATCH"
    PRICE_SAFETY_REJECTED = "PRICE_SAFETY_REJECTED"
    TERMINAL_OBLIGATION_MISMATCH = "TERMINAL_OBLIGATION_MISMATCH"
    UNSUPPORTED_RECEIPT_KIND = "UNSUPPORTED_RECEIPT_KIND"
    EMPTY_RECEIPT = "EMPTY_RECEIPT"
    JOURNAL_TOO_LARGE = "JOURNAL_TOO_LARGE"
    RECEIPT_VERIFICATION_FAILED = "RECEIPT_VERIFICATION_FAILED"


class ZDEXBuybackSpotReceiptRejectedV1(ValueError):
    """Stable fail-closed rejection from the shadow receipt boundary."""

    def __init__(
        self,
        code: ZDEXBuybackSpotReceiptRejectCodeV1,
        detail: str,
    ) -> None:
        if type(code) is not ZDEXBuybackSpotReceiptRejectCodeV1:
            raise TypeError("ZDEX buyback Spot reject code is not closed")
        if type(detail) is not str:
            raise TypeError("ZDEX buyback Spot reject detail must be exact str")
        self.code = code
        super().__init__(f"{code.value}: {detail}")


def _reject(
    code: ZDEXBuybackSpotReceiptRejectCodeV1,
    detail: str,
) -> NoReturn:
    raise ZDEXBuybackSpotReceiptRejectedV1(code, detail)


@dataclass(frozen=True, slots=True)
class ZDEXBuybackSpotSafetyPurchaseJournalV1:
    """Authenticated public facts for one governed exact-in Spot purchase.

    Amounts are unsigned integer atoms.  ``quote_amount_in_atoms`` is the
    selected spend ``q`` and ``purchased_zdex_atoms`` is the actual output
    ``p``.  The constructor derives both the safety binding and the closed
    terminal-obligation fact, removing those values from caller control.
    """

    chain_id: str
    deployment_root: str
    profile_root: str
    writer_epoch: int
    route_release_id: str
    command_occurrence_id: str
    global_pre_state_root: str
    spot_module_release_id: str
    spot_guest_image_id: str
    tokenomics_module_release_id: str
    tokenomics_pre_state_root: str
    spend_policy_root: str
    fee_policy_root: str
    fee_pre_state_root: str
    cadence_pre_state_root: str
    fee_context_root: str
    fee_command_root: str
    pre_spot_lane_root: str
    post_spot_lane_root: str
    pool_id: str
    pool_definition_root: str
    quote_asset_id: str
    zdex_asset_id: str
    oracle_policy_root: str
    oracle_id: str
    oracle_occurrence_root: str
    oracle_observed_height: int
    oracle_quote_numerator_atoms: int
    oracle_zdex_denominator_atoms: int
    quote_reserve_atoms: int
    zdex_reserve_atoms: int
    consensus_height: int
    route_safe_quote_limit_atoms: int
    quote_amount_in_atoms: int
    minimum_output_atoms: int
    purchased_zdex_atoms: int
    terminal_obligations_root: str = field(init=False)
    safety_binding_root: str = field(init=False)

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "terminal_obligations_root",
            hash_global_v1(
                "zdex-buyback-pending-burn-obligation-v1",
                {
                    "profile_root": self.profile_root,
                    "route_release_id": self.route_release_id,
                    "command_occurrence_id": self.command_occurrence_id,
                    "zdex_asset_id": self.zdex_asset_id,
                    "purchased_zdex_atoms": self.purchased_zdex_atoms,
                },
            ),
        )
        object.__setattr__(
            self,
            "safety_binding_root",
            hash_global_v1(
                "zdex-buyback-spot-safety-binding-v1",
                self._safety_binding_body(),
            ),
        )
        self.validate()

    def _safety_binding_body(self) -> dict[str, object]:
        return {
            "schema": ZDEX_BUYBACK_SPOT_SAFETY_PURCHASE_JOURNAL_SCHEMA_V1,
            "chain_id": self.chain_id,
            "deployment_root": self.deployment_root,
            "profile_root": self.profile_root,
            "writer_epoch": self.writer_epoch,
            "route_release_id": self.route_release_id,
            "command_occurrence_id": self.command_occurrence_id,
            "global_pre_state_root": self.global_pre_state_root,
            "spot_module_release_id": self.spot_module_release_id,
            "spot_guest_image_id": self.spot_guest_image_id,
            "tokenomics_module_release_id": self.tokenomics_module_release_id,
            "tokenomics_pre_state_root": self.tokenomics_pre_state_root,
            "spend_policy_root": self.spend_policy_root,
            "fee_policy_root": self.fee_policy_root,
            "fee_pre_state_root": self.fee_pre_state_root,
            "cadence_pre_state_root": self.cadence_pre_state_root,
            "fee_context_root": self.fee_context_root,
            "fee_command_root": self.fee_command_root,
            "pre_spot_lane_root": self.pre_spot_lane_root,
            "post_spot_lane_root": self.post_spot_lane_root,
            "pool_id": self.pool_id,
            "pool_definition_root": self.pool_definition_root,
            "quote_asset_id": self.quote_asset_id,
            "zdex_asset_id": self.zdex_asset_id,
            "oracle_policy_root": self.oracle_policy_root,
            "oracle_id": self.oracle_id,
            "oracle_occurrence_root": self.oracle_occurrence_root,
            "oracle_observed_height": self.oracle_observed_height,
            "oracle_quote_numerator_atoms": self.oracle_quote_numerator_atoms,
            "oracle_zdex_denominator_atoms": self.oracle_zdex_denominator_atoms,
            "quote_reserve_atoms": self.quote_reserve_atoms,
            "zdex_reserve_atoms": self.zdex_reserve_atoms,
            "consensus_height": self.consensus_height,
            "route_safe_quote_limit_atoms": self.route_safe_quote_limit_atoms,
            "quote_amount_in_atoms": self.quote_amount_in_atoms,
            "minimum_output_atoms": self.minimum_output_atoms,
            "purchased_zdex_atoms": self.purchased_zdex_atoms,
            "terminal_obligations_root": self.terminal_obligations_root,
        }

    def validate(self) -> None:
        string_fields = (
            "chain_id",
            "deployment_root",
            "profile_root",
            "route_release_id",
            "command_occurrence_id",
            "global_pre_state_root",
            "spot_module_release_id",
            "spot_guest_image_id",
            "tokenomics_module_release_id",
            "tokenomics_pre_state_root",
            "spend_policy_root",
            "fee_policy_root",
            "fee_pre_state_root",
            "cadence_pre_state_root",
            "fee_context_root",
            "fee_command_root",
            "pre_spot_lane_root",
            "post_spot_lane_root",
            "pool_id",
            "pool_definition_root",
            "quote_asset_id",
            "zdex_asset_id",
            "oracle_policy_root",
            "oracle_id",
            "oracle_occurrence_root",
            "terminal_obligations_root",
            "safety_binding_root",
        )
        if any(type(getattr(self, name)) is not str for name in string_fields):
            raise TypeError("ZDEX buyback Spot journal strings must be exact str")
        integer_fields = (
            "writer_epoch",
            "oracle_observed_height",
            "oracle_quote_numerator_atoms",
            "oracle_zdex_denominator_atoms",
            "quote_reserve_atoms",
            "zdex_reserve_atoms",
            "consensus_height",
            "route_safe_quote_limit_atoms",
            "quote_amount_in_atoms",
            "minimum_output_atoms",
            "purchased_zdex_atoms",
        )
        if any(type(getattr(self, name)) is not int for name in integer_fields):
            raise TypeError("ZDEX buyback Spot journal integers must be exact int")
        _require_token(self.chain_id, name="ZDEX buyback Spot chain id")
        _require_token(self.oracle_id, name="ZDEX buyback Spot oracle id")
        for name in (field_name for field_name in string_fields[1:] if field_name != "oracle_id"):
            _require_root(
                getattr(self, name),
                name=f"ZDEX buyback Spot {name}",
            )
        _require_nonnegative_int(self.writer_epoch, name="ZDEX buyback Spot writer epoch")
        _require_nonnegative_int(
            self.consensus_height,
            name="ZDEX buyback Spot consensus height",
        )
        for name in (
            "route_safe_quote_limit_atoms",
            "quote_amount_in_atoms",
            "minimum_output_atoms",
            "purchased_zdex_atoms",
        ):
            _require_atoms_u128(getattr(self, name), name=f"ZDEX buyback Spot {name}")
        for name in (
            "oracle_quote_numerator_atoms",
            "oracle_zdex_denominator_atoms",
            "quote_reserve_atoms",
            "zdex_reserve_atoms",
        ):
            value = _require_atoms_u128(
                getattr(self, name),
                name=f"ZDEX buyback Spot {name}",
            )
            if value == 0:
                raise ValueError(f"ZDEX buyback Spot {name} must be positive")
        _require_nonnegative_int(
            self.oracle_observed_height,
            name="ZDEX buyback Spot Oracle observed height",
        )
        if self.quote_asset_id == self.zdex_asset_id:
            raise ValueError("ZDEX buyback Spot assets must differ")
        if self.pre_spot_lane_root == self.post_spot_lane_root:
            raise ValueError("ZDEX buyback Spot transition must change the Spot root")
        if self.route_safe_quote_limit_atoms == 0 or self.quote_amount_in_atoms == 0:
            raise ValueError("ZDEX buyback Spot quote limits and spend must be positive")
        if self.minimum_output_atoms == 0 or self.purchased_zdex_atoms == 0:
            raise ValueError("ZDEX buyback Spot output amounts must be positive")
        if self.quote_amount_in_atoms > self.route_safe_quote_limit_atoms:
            raise ValueError("ZDEX buyback Spot spend exceeds the route-safe limit")
        if self.purchased_zdex_atoms < self.minimum_output_atoms:
            raise ValueError("ZDEX buyback Spot output is below the positive minimum")
        if (
            self.quote_amount_in_atoms > MAX_DELTA_ATOMS_V1
            or self.purchased_zdex_atoms > MAX_DELTA_ATOMS_V1
        ):
            raise ValueError("ZDEX buyback Spot amounts must fit signed effect atoms")
        expected_terminal = hash_global_v1(
            "zdex-buyback-pending-burn-obligation-v1",
            {
                "profile_root": self.profile_root,
                "route_release_id": self.route_release_id,
                "command_occurrence_id": self.command_occurrence_id,
                "zdex_asset_id": self.zdex_asset_id,
                "purchased_zdex_atoms": self.purchased_zdex_atoms,
            },
        )
        if self.terminal_obligations_root != expected_terminal:
            raise ValueError("ZDEX buyback pending burn obligation mismatch")
        expected_binding = hash_global_v1(
            "zdex-buyback-spot-safety-binding-v1",
            self._safety_binding_body(),
        )
        if self.safety_binding_root != expected_binding:
            raise ValueError("ZDEX buyback Spot safety binding root mismatch")

    @property
    def journal_root(self) -> str:
        self.validate()
        return hash_global_v1(
            "zdex-buyback-spot-safety-purchase-journal-v1",
            self.to_canonical(),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            **self._safety_binding_body(),
            "safety_binding_root": self.safety_binding_root,
        }


@dataclass(frozen=True, slots=True)
class ZDEXBuybackSpotReceiptEnvelopeV1:
    receipt_kind: ReceiptKindV1
    receipt_bytes: bytes

    def __post_init__(self) -> None:
        if type(self.receipt_kind) is not ReceiptKindV1:
            raise TypeError("ZDEX buyback Spot receipt kind is not closed")
        if type(self.receipt_bytes) is not bytes:
            raise TypeError("ZDEX buyback Spot receipt bytes must be exact bytes")


@dataclass(frozen=True, slots=True)
class ZDEXBuybackSpotReceiptCandidateV1:
    profile: EconomicProfileSnapshotV1
    policy_registry: EconomicPolicyRegistryV1
    buyback_policy: ZDEXBuybackExecutionPolicyV1
    spend_policy: ZDEXBuybackSpendPolicyV1
    price_policy: ZDEXBuybackPriceSafetyPolicyV1
    fee_policy: ZDEXFeeAllocationPolicyV1
    fee_context: ZDEXFeeAllocationContextV1
    fee_command: ZDEXFeeAllocationCommandV1
    occurrence: EconomicCommandOccurrenceV1
    global_pre_state: GlobalEconomicStateV1
    tokenomics_pre_state: ZDEXAtomicBuybackTokenomicsStateV1
    journal: ZDEXBuybackSpotSafetyPurchaseJournalV1
    receipt: ZDEXBuybackSpotReceiptEnvelopeV1

    def __post_init__(self) -> None:
        expected = (
            (self.profile, EconomicProfileSnapshotV1, "profile"),
            (self.policy_registry, EconomicPolicyRegistryV1, "policy registry"),
            (self.buyback_policy, ZDEXBuybackExecutionPolicyV1, "buyback policy"),
            (self.spend_policy, ZDEXBuybackSpendPolicyV1, "spend policy"),
            (self.price_policy, ZDEXBuybackPriceSafetyPolicyV1, "price policy"),
            (self.fee_policy, ZDEXFeeAllocationPolicyV1, "fee policy"),
            (self.fee_context, ZDEXFeeAllocationContextV1, "fee context"),
            (self.fee_command, ZDEXFeeAllocationCommandV1, "fee command"),
            (self.occurrence, EconomicCommandOccurrenceV1, "occurrence"),
            (self.global_pre_state, GlobalEconomicStateV1, "global pre-state"),
            (
                self.tokenomics_pre_state,
                ZDEXAtomicBuybackTokenomicsStateV1,
                "tokenomics pre-state",
            ),
            (self.journal, ZDEXBuybackSpotSafetyPurchaseJournalV1, "journal"),
            (self.receipt, ZDEXBuybackSpotReceiptEnvelopeV1, "receipt"),
        )
        for value, expected_type, label in expected:
            if type(value) is not expected_type:
                raise TypeError(f"ZDEX buyback Spot receipt {label} must be exact typed data")


@dataclass(frozen=True, slots=True)
class _ZDEXBuybackSpotReceiptSnapshotV1:
    profile: EconomicProfileSnapshotV1
    policy_registry: EconomicPolicyRegistryV1
    buyback_policy: ZDEXBuybackExecutionPolicyV1
    spend_policy: ZDEXBuybackSpendPolicyV1
    price_policy: ZDEXBuybackPriceSafetyPolicyV1
    fee_policy: ZDEXFeeAllocationPolicyV1
    fee_context: ZDEXFeeAllocationContextV1
    fee_command: ZDEXFeeAllocationCommandV1
    occurrence: EconomicCommandOccurrenceV1
    global_pre_state: GlobalEconomicStateV1
    tokenomics_pre_state: ZDEXAtomicBuybackTokenomicsStateV1
    journal: ZDEXBuybackSpotSafetyPurchaseJournalV1
    receipt: ZDEXBuybackSpotReceiptEnvelopeV1


def _snapshot_policy_registry_v1(
    registry: EconomicPolicyRegistryV1,
) -> EconomicPolicyRegistryV1:
    if type(registry) is not EconomicPolicyRegistryV1 or type(registry.bindings) is not tuple:
        raise TypeError("ZDEX buyback Spot policy registry must be exact typed data")
    bindings = []
    for binding in registry.bindings:
        if type(binding) is not EconomicPolicyBindingV1:
            raise TypeError("ZDEX buyback Spot policy binding must be exact typed data")
        _require_exact_dataclass_scalars_v1(
            binding,
            name="ZDEX buyback Spot policy binding",
        )
        bindings.append(replace(binding))
    return EconomicPolicyRegistryV1(tuple(bindings))


def _snapshot_buyback_policy_v1(
    policy: ZDEXBuybackExecutionPolicyV1,
) -> ZDEXBuybackExecutionPolicyV1:
    if type(policy) is not ZDEXBuybackExecutionPolicyV1:
        raise TypeError("ZDEX buyback Spot policy must be exact typed data")
    _require_exact_dataclass_scalars_v1(policy, name="ZDEX buyback Spot policy")
    return replace(policy)


def _snapshot_spend_policy_v1(
    policy: ZDEXBuybackSpendPolicyV1,
) -> ZDEXBuybackSpendPolicyV1:
    if type(policy) is not ZDEXBuybackSpendPolicyV1:
        raise TypeError("ZDEX buyback spend policy must be exact typed data")
    _require_exact_dataclass_scalars_v1(policy, name="ZDEX buyback spend policy")
    return replace(policy)


def _snapshot_price_policy_v1(
    policy: ZDEXBuybackPriceSafetyPolicyV1,
) -> ZDEXBuybackPriceSafetyPolicyV1:
    if type(policy) is not ZDEXBuybackPriceSafetyPolicyV1:
        raise TypeError("ZDEX buyback price policy must be exact typed data")
    _require_exact_dataclass_scalars_v1(policy, name="ZDEX buyback price policy")
    return replace(policy)


def _snapshot_tokenomics_pre_state_v1(
    state: ZDEXAtomicBuybackTokenomicsStateV1,
) -> ZDEXAtomicBuybackTokenomicsStateV1:
    if type(state) is not ZDEXAtomicBuybackTokenomicsStateV1:
        raise TypeError("ZDEX buyback tokenomics pre-state must be exact typed data")
    owned = deepcopy(state)
    owned.validate()
    return owned


def _snapshot_fee_context_v1(
    context: ZDEXFeeAllocationContextV1,
) -> ZDEXFeeAllocationContextV1:
    if type(context) is not ZDEXFeeAllocationContextV1:
        raise TypeError("ZDEX buyback fee context must be exact typed data")
    _require_exact_dataclass_scalars_v1(context, name="ZDEX buyback fee context")
    context.validate()
    return replace(context)


def _snapshot_fee_command_v1(
    command: ZDEXFeeAllocationCommandV1,
) -> ZDEXFeeAllocationCommandV1:
    if type(command) is not ZDEXFeeAllocationCommandV1:
        raise TypeError("ZDEX buyback fee command must be exact typed data")
    _require_exact_dataclass_scalars_v1(command, name="ZDEX buyback fee command")
    command.validate()
    return replace(command)


def _snapshot_journal_v1(
    journal: ZDEXBuybackSpotSafetyPurchaseJournalV1,
) -> ZDEXBuybackSpotSafetyPurchaseJournalV1:
    if type(journal) is not ZDEXBuybackSpotSafetyPurchaseJournalV1:
        raise TypeError("ZDEX buyback Spot journal must be exact typed data")
    _require_exact_dataclass_scalars_v1(journal, name="ZDEX buyback Spot journal")
    journal.validate()
    return replace(journal)


def _snapshot_candidate_v1(
    candidate: ZDEXBuybackSpotReceiptCandidateV1,
) -> _ZDEXBuybackSpotReceiptSnapshotV1:
    if type(candidate) is not ZDEXBuybackSpotReceiptCandidateV1:
        raise TypeError("ZDEX buyback Spot candidate must be exact typed data")
    candidate.__post_init__()
    return _ZDEXBuybackSpotReceiptSnapshotV1(
        profile=snapshot_economic_profile_v1(candidate.profile),
        policy_registry=_snapshot_policy_registry_v1(candidate.policy_registry),
        buyback_policy=_snapshot_buyback_policy_v1(candidate.buyback_policy),
        spend_policy=_snapshot_spend_policy_v1(candidate.spend_policy),
        price_policy=_snapshot_price_policy_v1(candidate.price_policy),
        fee_policy=_snapshot_fee_policy_v1(candidate.fee_policy),
        fee_context=_snapshot_fee_context_v1(candidate.fee_context),
        fee_command=_snapshot_fee_command_v1(candidate.fee_command),
        occurrence=_snapshot_occurrence_v1(candidate.occurrence),
        global_pre_state=_snapshot_state_v1(candidate.global_pre_state),
        tokenomics_pre_state=_snapshot_tokenomics_pre_state_v1(candidate.tokenomics_pre_state),
        journal=_snapshot_journal_v1(candidate.journal),
        receipt=ZDEXBuybackSpotReceiptEnvelopeV1(
            candidate.receipt.receipt_kind,
            candidate.receipt.receipt_bytes,
        ),
    )


def _select_shadow_route_and_release_v1(
    owned: _ZDEXBuybackSpotReceiptSnapshotV1,
) -> tuple[RouteReleaseV1, LaneModuleReleaseV1, LaneModuleReleaseV1]:
    profile = owned.profile
    if profile.status is not ProfileStatusV1.SHADOW:
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.SHADOW_PROFILE_REQUIRED,
            "profile must remain SHADOW",
        )
    routes = tuple(
        route
        for route in profile.route_registry.routes
        if route.command_kind == PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1
    )
    if len(routes) != 1:
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.GOVERNED_ROUTE_MISMATCH,
            "profile must select exactly one buyback route",
        )
    route = routes[0]
    expected_shape = (LaneIdV1.SPOT_LIQUIDITY, LaneIdV1.ZDEX_TOKENOMICS)
    expected_roles = (AMM_PURCHASE_OUTPUT_ROLE_V1, ZDEX_BURN_INPUT_ROLE_V1)
    expected_ports = (
        zdex_amm_purchase_port_schema_root_v1(),
        zdex_burn_port_schema_root_v1(),
    )
    if (
        route.status is not ReleaseStatusV1.SHADOW
        or route.accepts_new_objects
        or route.ordered_lanes != expected_shape
        or route.dependency_roles != expected_roles
        or route.port_schema_roots != expected_ports
    ):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.GOVERNED_ROUTE_MISMATCH,
            "buyback route shape or status mismatch",
        )
    release = profile.lane_registry.release_for(LaneIdV1.SPOT_LIQUIDITY)
    tokenomics_release = profile.lane_registry.release_for(LaneIdV1.ZDEX_TOKENOMICS)
    if (
        release.status is not ReleaseStatusV1.SHADOW
        or release.accepts_new_objects
        or route.module_release_ids[0] != release.release_id
        or PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1 not in release.command_variants
    ):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.GOVERNED_SPOT_RELEASE_MISMATCH,
            "profile-selected Spot release mismatch",
        )
    if (
        tokenomics_release.status is not ReleaseStatusV1.SHADOW
        or tokenomics_release.accepts_new_objects
        or route.module_release_ids[1] != tokenomics_release.release_id
        or PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1 not in tokenomics_release.command_variants
    ):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.GOVERNED_SPOT_RELEASE_MISMATCH,
            "profile-selected tokenomics release mismatch",
        )
    return route, release, tokenomics_release


def _require_governed_policy_v1(
    owned: _ZDEXBuybackSpotReceiptSnapshotV1,
    route: RouteReleaseV1,
) -> None:
    if owned.profile.policy_registry_root != owned.policy_registry.registry_root:
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.GOVERNED_POLICY_MISMATCH,
            "policy registry is outside the selected profile",
        )
    try:
        execution_binding = owned.policy_registry.require_binding(
            policy_kind=ZDEX_BUYBACK_EXECUTION_POLICY_KIND_V1,
            command_kind=PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
        )
        spend_binding = owned.policy_registry.require_binding(
            policy_kind=ZDEX_BUYBACK_SPEND_POLICY_KIND_V1,
            command_kind=PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
        )
        price_binding = owned.policy_registry.require_binding(
            policy_kind=ZDEX_BUYBACK_PRICE_SAFETY_POLICY_KIND_V1,
            command_kind=PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
        )
        fee_binding = owned.policy_registry.require_binding(
            policy_kind=ZDEX_FEE_ALLOCATION_POLICY_KIND_V1,
            command_kind=PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
        )
    except ValueError:
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.GOVERNED_POLICY_MISMATCH,
            "buyback execution policy binding is absent",
        )
    journal = owned.journal
    policy = owned.buyback_policy
    if (
        execution_binding.policy_root != policy.policy_root
        or spend_binding.policy_root != owned.spend_policy.policy_root
        or price_binding.policy_root != owned.price_policy.policy_root
        or fee_binding.policy_root != owned.fee_policy.policy_root
        or owned.spend_policy.quote_asset_id != policy.quote_asset_id
        or journal.pool_id != policy.pool_id
        or journal.pool_definition_root != policy.pool_definition_root
        or journal.quote_asset_id != policy.quote_asset_id
        or journal.zdex_asset_id != policy.zdex_asset_id
        or journal.oracle_id != owned.price_policy.oracle_id
        or journal.oracle_policy_root != route.oracle_policy_root
        or route.oracle_policy_root != owned.price_policy.policy_root
    ):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.GOVERNED_POLICY_MISMATCH,
            "journal resources are outside the governed buyback policy",
        )


def _require_occurrence_bindings_v1(
    owned: _ZDEXBuybackSpotReceiptSnapshotV1,
    route: RouteReleaseV1,
    release: LaneModuleReleaseV1,
    tokenomics_release: LaneModuleReleaseV1,
) -> None:
    occurrence = owned.occurrence
    journal = owned.journal
    if (
        occurrence.command_kind != PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1
        or occurrence.route_release_id != route.route_release_id
        or occurrence.profile_root != owned.profile.profile_id
    ):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.OCCURRENCE_BINDING_MISMATCH,
            "occurrence is outside the selected profile or route",
        )
    expected = (
        (journal.chain_id, occurrence.chain_id),
        (journal.deployment_root, occurrence.deployment_root),
        (journal.profile_root, occurrence.profile_root),
        (journal.writer_epoch, owned.profile.authority_epoch),
        (journal.route_release_id, route.route_release_id),
        (journal.command_occurrence_id, occurrence.occurrence_id),
        (journal.spot_module_release_id, release.release_id),
        (journal.spot_guest_image_id, release.guest_image_id),
        (journal.tokenomics_module_release_id, tokenomics_release.release_id),
        (journal.consensus_height, occurrence.height),
    )
    if any(actual != wanted for actual, wanted in expected):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.OCCURRENCE_BINDING_MISMATCH,
            "journal occurrence or release coordinate mismatch",
        )
    fee_context = owned.fee_context
    if (
        fee_context.chain_id != occurrence.chain_id
        or fee_context.deployment_root != occurrence.deployment_root
        or fee_context.profile_root != occurrence.profile_root
        or fee_context.writer_epoch != owned.profile.authority_epoch
        or fee_context.allocation_route_release_id != route.route_release_id
        or fee_context.authorized_buyback_route_release_id != route.route_release_id
        or fee_context.tokenomics_module_release_id != tokenomics_release.release_id
        or fee_context.command_occurrence_id != occurrence.occurrence_id
        or fee_context.policy_root != owned.fee_policy.policy_root
    ):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.OCCURRENCE_BINDING_MISMATCH,
            "fee command context is outside the same governed occurrence",
        )


def _require_state_and_oracle_bindings_v1(
    owned: _ZDEXBuybackSpotReceiptSnapshotV1,
) -> VerifiedZDEXBuybackPriceSafetyV1:
    journal = owned.journal
    state = owned.global_pre_state
    occurrence = owned.occurrence
    if (
        state.state_root != occurrence.pre_state_root
        or journal.global_pre_state_root != state.state_root
        or state.chain_id != occurrence.chain_id
        or state.deployment_root != occurrence.deployment_root
        or state.profile_root != occurrence.profile_root
        or state.writer_epoch != journal.writer_epoch
    ):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.STATE_ROOT_BINDING_MISMATCH,
            "global pre-state is stale or outside the occurrence",
        )
    spot = next(row for row in state.lane_roots if row.lane_id is LaneIdV1.SPOT_LIQUIDITY)
    if (
        spot.lane_id is not LaneIdV1.SPOT_LIQUIDITY
        or spot.enabled
        or spot.module_release_id != journal.spot_module_release_id
        or spot.state_root != journal.pre_spot_lane_root
    ):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.STATE_ROOT_BINDING_MISMATCH,
            "Spot shadow pre-root is outside the disabled global lane commitment",
        )
    tokenomics = next(row for row in state.lane_roots if row.lane_id is LaneIdV1.ZDEX_TOKENOMICS)
    fee_state = owned.tokenomics_pre_state.fee_state_for(journal.quote_asset_id)
    cadence_state = owned.tokenomics_pre_state.cadence_state_for(journal.quote_asset_id)
    derived_fee_command = ZDEXFeeAllocationCommandV1(fee_state.fee_ingress_atoms)
    if (
        tokenomics.enabled
        or tokenomics.module_release_id != journal.tokenomics_module_release_id
        or tokenomics.state_root != owned.tokenomics_pre_state.state_root
        or journal.tokenomics_pre_state_root != tokenomics.state_root
        or journal.spend_policy_root != owned.spend_policy.policy_root
        or journal.fee_policy_root != owned.fee_policy.policy_root
        or journal.fee_pre_state_root != fee_state.state_root
        or journal.cadence_pre_state_root != cadence_state.state_root
        or owned.fee_command != derived_fee_command
        or journal.fee_context_root
        != hash_global_v1(
            "zdex-fee-allocation-context-v1",
            owned.fee_context.to_canonical(),
        )
        or journal.fee_command_root
        != hash_global_v1(
            "zdex-fee-allocation-command-v1",
            {"fee_charged_atoms": derived_fee_command.fee_charged_atoms},
        )
    ):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.STATE_ROOT_BINDING_MISMATCH,
            "tokenomics policy or pre-state is outside the global lane commitment",
        )
    oracle = next(
        (row for row in state.oracle_occurrences if row.oracle_id == journal.oracle_id),
        None,
    )
    if (
        oracle is None
        or oracle.occurrence_root != journal.oracle_occurrence_root
        or oracle.observed_height != journal.oracle_observed_height
        or not oracle.finalized
        or oracle.observed_height > occurrence.height
    ):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.ORACLE_BINDING_MISMATCH,
            "Oracle occurrence is absent, unfinalized, future, or substituted",
        )
    quote_pool_principal = zdex_pool_reserve_principal_v1(
        pool_id=owned.buyback_policy.pool_id,
        asset_id=owned.buyback_policy.quote_asset_id,
    )
    zdex_pool_principal = zdex_pool_reserve_principal_v1(
        pool_id=owned.buyback_policy.pool_id,
        asset_id=owned.buyback_policy.zdex_asset_id,
    )
    reserve_amounts = {
        (row.owner, row.asset, row.custody_domain): row.amount_atoms
        for row in state.custody
    }
    if (
        reserve_amounts.get(
            (
                quote_pool_principal,
                journal.quote_asset_id,
                AMM_POOL_CUSTODY_DOMAIN_V1,
            )
        )
        != journal.quote_reserve_atoms
        or reserve_amounts.get(
            (
                zdex_pool_principal,
                journal.zdex_asset_id,
                AMM_POOL_CUSTODY_DOMAIN_V1,
            )
        )
        != journal.zdex_reserve_atoms
    ):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.STATE_ROOT_BINDING_MISMATCH,
            "price-safety reserves are outside the committed pool accounting rows",
        )
    price_result = verify_zdex_buyback_price_safety_v1(
        owned.price_policy,
        ZDEXBuybackPriceSafetyObservationV1(
            oracle_occurrence_root=journal.oracle_occurrence_root,
            current_height=journal.consensus_height,
            oracle_observed_height=journal.oracle_observed_height,
            oracle_quote_numerator_atoms=journal.oracle_quote_numerator_atoms,
            oracle_zdex_denominator_atoms=journal.oracle_zdex_denominator_atoms,
            quote_reserve_atoms=journal.quote_reserve_atoms,
            zdex_reserve_atoms=journal.zdex_reserve_atoms,
            quote_amount_in_atoms=journal.quote_amount_in_atoms,
            purchased_zdex_atoms=journal.purchased_zdex_atoms,
            claimed_route_safe_quote_limit_atoms=(
                journal.route_safe_quote_limit_atoms
            ),
            claimed_minimum_output_atoms=journal.minimum_output_atoms,
        ),
    )
    if isinstance(price_result, ZDEXBuybackPriceSafetyRejectedV1):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.PRICE_SAFETY_REJECTED,
            f"integer price envelope rejected with {price_result.code.value}",
        )
    return price_result


@dataclass(frozen=True, slots=True)
class _VerifiedZDEXBuybackSpotFieldsV1:
    journal: ZDEXBuybackSpotSafetyPurchaseJournalV1
    journal_digest: str
    expected_image_id: str
    receipt_digest: str
    receipt_kind: ReceiptKindV1
    tokenomics_pre_state: ZDEXAtomicBuybackTokenomicsStateV1
    spend_policy: ZDEXBuybackSpendPolicyV1
    fee_policy: ZDEXFeeAllocationPolicyV1
    fee_context: ZDEXFeeAllocationContextV1
    fee_command: ZDEXFeeAllocationCommandV1
    fee_ingress: VerifiedZDEXFeeIngressSliceV1
    price_safety: VerifiedZDEXBuybackPriceSafetyV1
    authority_head_root: str
    verifier_binding_root: str

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": VERIFIED_ZDEX_BUYBACK_SPOT_SAFETY_PURCHASE_SCHEMA_V1,
            "journal_root": self.journal.journal_root,
            "journal_digest": self.journal_digest,
            "expected_image_id": self.expected_image_id,
            "receipt_digest": self.receipt_digest,
            "receipt_kind": self.receipt_kind,
            "tokenomics_pre_state_root": self.tokenomics_pre_state.state_root,
            "spend_policy_root": self.spend_policy.policy_root,
            "fee_policy_root": self.fee_policy.policy_root,
            "fee_context_root": hash_global_v1(
                "zdex-fee-allocation-context-v1",
                self.fee_context.to_canonical(),
            ),
            "fee_command_root": hash_global_v1(
                "zdex-fee-allocation-command-v1",
                {"fee_charged_atoms": self.fee_command.fee_charged_atoms},
            ),
            "fee_ingress_binding_root": self.fee_ingress.binding_root,
            "price_safety_binding_root": self.price_safety.binding_root,
            "authority_head_root": self.authority_head_root,
            "verifier_binding_root": self.verifier_binding_root,
        }


class VerifiedZDEXBuybackSpotSafetyPurchaseV1:
    """Opaque process-local witness for one authenticated shadow journal."""

    _fields: _VerifiedZDEXBuybackSpotFieldsV1
    __slots__ = ("_fields",)

    def __init__(
        self,
        token: object,
        fields: _VerifiedZDEXBuybackSpotFieldsV1,
    ) -> None:
        if token is not _VERIFIED_ZDEX_BUYBACK_SPOT_TOKEN_V1:
            raise TypeError("VerifiedZDEXBuybackSpotSafetyPurchaseV1 is verifier-constructed")
        if type(fields) is not _VerifiedZDEXBuybackSpotFieldsV1:
            raise TypeError("verified ZDEX buyback Spot fields must be exact typed data")
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("VerifiedZDEXBuybackSpotSafetyPurchaseV1 is immutable")

    @property
    def journal(self) -> ZDEXBuybackSpotSafetyPurchaseJournalV1:
        return replace(self._fields.journal)

    @property
    def journal_root(self) -> str:
        return self._fields.journal.journal_root

    @property
    def journal_digest(self) -> str:
        return self._fields.journal_digest

    @property
    def expected_image_id(self) -> str:
        return self._fields.expected_image_id

    @property
    def receipt_digest(self) -> str:
        return self._fields.receipt_digest

    @property
    def receipt_kind(self) -> ReceiptKindV1:
        return self._fields.receipt_kind

    @property
    def tokenomics_pre_state(self) -> ZDEXAtomicBuybackTokenomicsStateV1:
        return deepcopy(self._fields.tokenomics_pre_state)

    @property
    def spend_policy(self) -> ZDEXBuybackSpendPolicyV1:
        return replace(self._fields.spend_policy)

    @property
    def fee_policy(self) -> ZDEXFeeAllocationPolicyV1:
        return deepcopy(self._fields.fee_policy)

    @property
    def fee_context(self) -> ZDEXFeeAllocationContextV1:
        return replace(self._fields.fee_context)

    @property
    def fee_command(self) -> ZDEXFeeAllocationCommandV1:
        return replace(self._fields.fee_command)

    @property
    def fee_ingress(self) -> VerifiedZDEXFeeIngressSliceV1:
        return self._fields.fee_ingress

    @property
    def price_safety(self) -> VerifiedZDEXBuybackPriceSafetyV1:
        return self._fields.price_safety

    @property
    def authority_head_root(self) -> str:
        return self._fields.authority_head_root

    @property
    def verifier_binding_root(self) -> str:
        return self._fields.verifier_binding_root

    @property
    def binding_root(self) -> str:
        return hash_global_v1(
            "verified-zdex-buyback-spot-safety-purchase-v1",
            self._fields.to_canonical(),
        )


def verify_zdex_buyback_spot_safety_receipt_shadow_v1(
    candidate: ZDEXBuybackSpotReceiptCandidateV1,
    *,
    authority_head: GlobalEconomicAuthorityHeadV1,
    receipt_verifier: BoundEconomicReceiptVerifierV1,
) -> VerifiedZDEXBuybackSpotSafetyPurchaseV1:
    """Verify exact shadow receipt bindings and return an opaque witness.

    Reject precedence is candidate ownership, governed selection, occurrence,
    state/Oracle freshness, receipt profile/size, then the external receipt
    callback.  Any callback exception or non-``None`` result rejects without
    creating a witness.  This pure function performs no publication or IO.
    """

    try:
        owned = _snapshot_candidate_v1(candidate)
    except (TypeError, ValueError):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.MALFORMED_CANDIDATE,
            "candidate ownership or invariant validation failed",
        )
    route, release, tokenomics_release = _select_shadow_route_and_release_v1(owned)
    if (
        type(authority_head) is not GlobalEconomicAuthorityHeadV1
        or type(receipt_verifier) is not BoundEconomicReceiptVerifierV1
        or authority_head.status is not GlobalEconomicAuthorityStatusV1.ACTIVE
        or authority_head.chain_id != owned.occurrence.chain_id
        or authority_head.deployment_root != owned.occurrence.deployment_root
        or authority_head.profile_root != owned.profile.profile_id
        or authority_head.writer_epoch != owned.profile.authority_epoch
        or authority_head.verifier_registry_root != owned.profile.verifier_registry_root
        or authority_head.verifier_release_id != receipt_verifier.release_id
        or authority_head.verifier_binding_root != receipt_verifier.binding_root
        or authority_head.root_image_id != owned.profile.root_image_id
    ):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.AUTHORITY_BINDING_MISMATCH,
            "receipt verifier is outside the current authority head",
        )
    try:
        receipt_verifier.require_binding(
            verifier_registry_root=authority_head.verifier_registry_root,
            deployment_root=authority_head.deployment_root,
            profile_root=authority_head.profile_root,
            root_image_id=authority_head.root_image_id,
            selection_purpose=EconomicReceiptVerifierSelectionPurposeV1.RESEARCH_SHADOW,
        )
    except (TypeError, ValueError):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.AUTHORITY_BINDING_MISMATCH,
            "receipt verifier deployment binding mismatch",
        )
    _require_governed_policy_v1(owned, route)
    _require_occurrence_bindings_v1(owned, route, release, tokenomics_release)
    price_safety = _require_state_and_oracle_bindings_v1(owned)
    receipt = owned.receipt
    if receipt.receipt_kind is not ReceiptKindV1.SUCCINCT:
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.UNSUPPORTED_RECEIPT_KIND,
            "only Succinct receipts are admissible",
        )
    if not receipt.receipt_bytes:
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.EMPTY_RECEIPT,
            "receipt bytes must be nonempty",
        )
    journal_bytes = canonical_global_bytes_v1(owned.journal)
    if len(journal_bytes) > min(route.max_journal_bytes, release.max_journal_bytes):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.JOURNAL_TOO_LARGE,
            "canonical journal exceeds the selected release ceiling",
        )
    try:
        receipt_verifier.verify_profile_lane_receipt(
            receipt.receipt_bytes,
            profile=owned.profile,
            lane_id=LaneIdV1.SPOT_LIQUIDITY,
            expected_module_release_id=release.release_id,
            expected_image_id=release.guest_image_id,
            expected_journal_bytes=journal_bytes,
        )
    except Exception:
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.RECEIPT_VERIFICATION_FAILED,
            "receipt callback rejected or failed",
        )
    fee_state = owned.tokenomics_pre_state.fee_state_for(owned.journal.quote_asset_id)
    fee_ingress = _derive_verified_zdex_fee_ingress_slice_v1(
        command_occurrence_id=owned.occurrence.occurrence_id,
        global_pre_state_root=owned.global_pre_state.state_root,
        profile_root=owned.profile.profile_id,
        fee_state=fee_state,
        authority_head_root=authority_head.authority_root,
        verifier_binding_root=receipt_verifier.binding_root,
    )
    fields = _VerifiedZDEXBuybackSpotFieldsV1(
        journal=owned.journal,
        journal_digest="0x" + hashlib.sha256(journal_bytes).hexdigest(),
        expected_image_id=release.guest_image_id,
        receipt_digest="0x" + hashlib.sha256(receipt.receipt_bytes).hexdigest(),
        receipt_kind=receipt.receipt_kind,
        tokenomics_pre_state=owned.tokenomics_pre_state,
        spend_policy=owned.spend_policy,
        fee_policy=owned.fee_policy,
        fee_context=owned.fee_context,
        fee_command=ZDEXFeeAllocationCommandV1(fee_ingress.fee_ingress_atoms),
        fee_ingress=fee_ingress,
        price_safety=price_safety,
        authority_head_root=authority_head.authority_root,
        verifier_binding_root=receipt_verifier.binding_root,
    )
    return VerifiedZDEXBuybackSpotSafetyPurchaseV1(
        _VERIFIED_ZDEX_BUYBACK_SPOT_TOKEN_V1,
        fields,
    )


__all__ = [
    "VERIFIED_ZDEX_BUYBACK_SPOT_SAFETY_PURCHASE_SCHEMA_V1",
    "ZDEX_BUYBACK_SPOT_SAFETY_PURCHASE_JOURNAL_SCHEMA_V1",
    "VerifiedZDEXBuybackSpotSafetyPurchaseV1",
    "ZDEXBuybackSpotReceiptCandidateV1",
    "ZDEXBuybackSpotReceiptEnvelopeV1",
    "ZDEXBuybackSpotReceiptRejectCodeV1",
    "ZDEXBuybackSpotReceiptRejectedV1",
    "ZDEXBuybackSpotSafetyPurchaseJournalV1",
    "verify_zdex_buyback_spot_safety_receipt_shadow_v1",
]
