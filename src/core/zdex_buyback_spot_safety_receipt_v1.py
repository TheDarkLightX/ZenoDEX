"""Shadow receipt boundary for a governed ZDEX buyback Spot purchase.

This module authenticates one minimum-sufficient public journal under the Spot
image selected by a complete SHADOW economic profile.  It creates no route,
publishes no state, and grants no value-moving authority.  The callback is the
cryptographic authority for the exact ``(image_id, canonical_journal_bytes)``
claim; every host-side input is copied and revalidated before that callback.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, field, replace
from enum import Enum
from typing import Final, NoReturn, Protocol

from .global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from .global_economic_proof_v1 import EconomicCommandOccurrenceV1, ReceiptKindV1
from .global_economic_refinement_snapshot_v1 import (
    _require_exact_dataclass_scalars_v1,
    _snapshot_occurrence_v1,
    _snapshot_state_v1,
)
from .global_settlement_types_v1 import (
    MAX_DELTA_ATOMS_V1,
    ZERO_ROOT_V1,
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
from .zdex_purchase_burn_route_types_v1 import (
    AMM_PURCHASE_OUTPUT_ROLE_V1,
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    ZDEX_BURN_INPUT_ROLE_V1,
    ZDEX_BUYBACK_EXECUTION_POLICY_KIND_V1,
    ZDEXBuybackExecutionPolicyV1,
    zdex_amm_purchase_port_schema_root_v1,
    zdex_burn_port_schema_root_v1,
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
    SHADOW_PROFILE_REQUIRED = "SHADOW_PROFILE_REQUIRED"
    GOVERNED_ROUTE_MISMATCH = "GOVERNED_ROUTE_MISMATCH"
    GOVERNED_SPOT_RELEASE_MISMATCH = "GOVERNED_SPOT_RELEASE_MISMATCH"
    GOVERNED_POLICY_MISMATCH = "GOVERNED_POLICY_MISMATCH"
    OCCURRENCE_BINDING_MISMATCH = "OCCURRENCE_BINDING_MISMATCH"
    STATE_ROOT_BINDING_MISMATCH = "STATE_ROOT_BINDING_MISMATCH"
    ORACLE_BINDING_MISMATCH = "ORACLE_BINDING_MISMATCH"
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
    pre_spot_lane_root: str
    post_spot_lane_root: str
    pool_id: str
    pool_definition_root: str
    quote_asset_id: str
    zdex_asset_id: str
    oracle_policy_root: str
    oracle_id: str
    oracle_occurrence_root: str
    consensus_height: int
    route_safe_quote_limit_atoms: int
    quote_amount_in_atoms: int
    minimum_output_atoms: int
    purchased_zdex_atoms: int
    terminal_obligations_root: str = field(init=False)
    safety_binding_root: str = field(init=False)

    def __post_init__(self) -> None:
        object.__setattr__(self, "terminal_obligations_root", ZERO_ROOT_V1)
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
            "pre_spot_lane_root": self.pre_spot_lane_root,
            "post_spot_lane_root": self.post_spot_lane_root,
            "pool_id": self.pool_id,
            "pool_definition_root": self.pool_definition_root,
            "quote_asset_id": self.quote_asset_id,
            "zdex_asset_id": self.zdex_asset_id,
            "oracle_policy_root": self.oracle_policy_root,
            "oracle_id": self.oracle_id,
            "oracle_occurrence_root": self.oracle_occurrence_root,
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
        for name in (
            field_name for field_name in string_fields[1:] if field_name != "oracle_id"
        ):
            _require_root(
                getattr(self, name),
                name=f"ZDEX buyback Spot {name}",
                allow_zero=name == "terminal_obligations_root",
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
        if self.terminal_obligations_root != ZERO_ROOT_V1:
            raise ValueError("ZDEX buyback Spot terminal obligations must be closed")
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


class ZDEXBuybackSpotSuccinctReceiptVerifierV1(Protocol):
    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> object | None: ...


@dataclass(frozen=True, slots=True)
class ZDEXBuybackSpotReceiptCandidateV1:
    profile: EconomicProfileSnapshotV1
    policy_registry: EconomicPolicyRegistryV1
    buyback_policy: ZDEXBuybackExecutionPolicyV1
    occurrence: EconomicCommandOccurrenceV1
    global_pre_state: GlobalEconomicStateV1
    journal: ZDEXBuybackSpotSafetyPurchaseJournalV1
    receipt: ZDEXBuybackSpotReceiptEnvelopeV1

    def __post_init__(self) -> None:
        expected = (
            (self.profile, EconomicProfileSnapshotV1, "profile"),
            (self.policy_registry, EconomicPolicyRegistryV1, "policy registry"),
            (self.buyback_policy, ZDEXBuybackExecutionPolicyV1, "buyback policy"),
            (self.occurrence, EconomicCommandOccurrenceV1, "occurrence"),
            (self.global_pre_state, GlobalEconomicStateV1, "global pre-state"),
            (self.journal, ZDEXBuybackSpotSafetyPurchaseJournalV1, "journal"),
            (self.receipt, ZDEXBuybackSpotReceiptEnvelopeV1, "receipt"),
        )
        for value, expected_type, label in expected:
            if type(value) is not expected_type:
                raise TypeError(
                    f"ZDEX buyback Spot receipt {label} must be exact typed data"
                )
@dataclass(frozen=True, slots=True)
class _ZDEXBuybackSpotReceiptSnapshotV1:
    profile: EconomicProfileSnapshotV1
    policy_registry: EconomicPolicyRegistryV1
    buyback_policy: ZDEXBuybackExecutionPolicyV1
    occurrence: EconomicCommandOccurrenceV1
    global_pre_state: GlobalEconomicStateV1
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
        occurrence=_snapshot_occurrence_v1(candidate.occurrence),
        global_pre_state=_snapshot_state_v1(candidate.global_pre_state),
        journal=_snapshot_journal_v1(candidate.journal),
        receipt=ZDEXBuybackSpotReceiptEnvelopeV1(
            candidate.receipt.receipt_kind,
            candidate.receipt.receipt_bytes,
        ),
    )


def _select_shadow_route_and_release_v1(
    owned: _ZDEXBuybackSpotReceiptSnapshotV1,
) -> tuple[RouteReleaseV1, LaneModuleReleaseV1]:
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
    return route, release


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
        binding = owned.policy_registry.require_binding(
            policy_kind=ZDEX_BUYBACK_EXECUTION_POLICY_KIND_V1,
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
        binding.policy_root != policy.policy_root
        or journal.pool_id != policy.pool_id
        or journal.pool_definition_root != policy.pool_definition_root
        or journal.quote_asset_id != policy.quote_asset_id
        or journal.zdex_asset_id != policy.zdex_asset_id
        or journal.oracle_policy_root != route.oracle_policy_root
    ):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.GOVERNED_POLICY_MISMATCH,
            "journal resources are outside the governed buyback policy",
        )


def _require_occurrence_bindings_v1(
    owned: _ZDEXBuybackSpotReceiptSnapshotV1,
    route: RouteReleaseV1,
    release: LaneModuleReleaseV1,
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
        (journal.consensus_height, occurrence.height),
    )
    if any(actual != wanted for actual, wanted in expected):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.OCCURRENCE_BINDING_MISMATCH,
            "journal occurrence or release coordinate mismatch",
        )


def _require_state_and_oracle_bindings_v1(
    owned: _ZDEXBuybackSpotReceiptSnapshotV1,
) -> None:
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
    spot = next(
        row for row in state.lane_roots if row.lane_id is LaneIdV1.SPOT_LIQUIDITY
    )
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
    oracle = next(
        (row for row in state.oracle_occurrences if row.oracle_id == journal.oracle_id),
        None,
    )
    if (
        oracle is None
        or oracle.occurrence_root != journal.oracle_occurrence_root
        or not oracle.finalized
        or oracle.observed_height > occurrence.height
    ):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.ORACLE_BINDING_MISMATCH,
            "Oracle occurrence is absent, unfinalized, future, or substituted",
        )
    if journal.terminal_obligations_root != ZERO_ROOT_V1:
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.TERMINAL_OBLIGATION_MISMATCH,
            "authenticated terminal obligations are not closed",
        )


@dataclass(frozen=True, slots=True)
class _VerifiedZDEXBuybackSpotFieldsV1:
    journal: ZDEXBuybackSpotSafetyPurchaseJournalV1
    journal_digest: str
    expected_image_id: str
    receipt_digest: str
    receipt_kind: ReceiptKindV1

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": VERIFIED_ZDEX_BUYBACK_SPOT_SAFETY_PURCHASE_SCHEMA_V1,
            "journal_root": self.journal.journal_root,
            "journal_digest": self.journal_digest,
            "expected_image_id": self.expected_image_id,
            "receipt_digest": self.receipt_digest,
            "receipt_kind": self.receipt_kind,
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
            raise TypeError(
                "VerifiedZDEXBuybackSpotSafetyPurchaseV1 is verifier-constructed"
            )
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
    def binding_root(self) -> str:
        return hash_global_v1(
            "verified-zdex-buyback-spot-safety-purchase-v1",
            self._fields.to_canonical(),
        )


def verify_zdex_buyback_spot_safety_receipt_shadow_v1(
    candidate: ZDEXBuybackSpotReceiptCandidateV1,
    receipt_verifier: ZDEXBuybackSpotSuccinctReceiptVerifierV1,
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
    route, release = _select_shadow_route_and_release_v1(owned)
    _require_governed_policy_v1(owned, route)
    _require_occurrence_bindings_v1(owned, route, release)
    _require_state_and_oracle_bindings_v1(owned)
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
    fields = _VerifiedZDEXBuybackSpotFieldsV1(
        journal=owned.journal,
        journal_digest="0x" + hashlib.sha256(journal_bytes).hexdigest(),
        expected_image_id=release.guest_image_id,
        receipt_digest="0x" + hashlib.sha256(receipt.receipt_bytes).hexdigest(),
        receipt_kind=receipt.receipt_kind,
    )
    try:
        callback_result = receipt_verifier.verify_succinct_receipt(
            receipt.receipt_bytes,
            expected_image_id=release.guest_image_id,
            expected_journal_bytes=journal_bytes,
        )
    except Exception:
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.RECEIPT_VERIFICATION_FAILED,
            "receipt callback rejected or failed",
        )
    if callback_result is not None:
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.RECEIPT_VERIFICATION_FAILED,
            "receipt callback violated the exact None success contract",
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
    "ZDEXBuybackSpotSuccinctReceiptVerifierV1",
    "verify_zdex_buyback_spot_safety_receipt_shadow_v1",
]
