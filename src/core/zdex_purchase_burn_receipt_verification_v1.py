"""Receipt admission for the two leaf outputs of ZDEX purchase-to-burn."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, replace
from typing import Final, Protocol

from .economic_receipt_verifier_deployment_v1 import BoundEconomicReceiptVerifierV1
from .economic_receipt_verifier_registry_v1 import (
    EconomicReceiptVerifierSelectionPurposeV1,
)
from .global_economic_authority_head_v1 import (
    GlobalEconomicAuthorityHeadV1,
    GlobalEconomicAuthorityStatusV1,
)
from .global_economic_capability_profile_binding_v1 import (
    snapshot_economic_policy_registry_v1,
)
from .global_economic_profile_snapshot_v1 import (
    _snapshot_lane_release_v1,
    _snapshot_route_release_v1,
    snapshot_economic_profile_v1,
)
from .global_economic_proof_v1 import EconomicCommandOccurrenceV1, ReceiptKindV1
from .global_economic_refinement_snapshot_v1 import (
    _require_exact_dataclass_scalars_v1,
    _snapshot_effect_plan_v1,
    _snapshot_occurrence_v1,
    _snapshot_state_v1,
)
from .global_settlement_types_v1 import (
    ZERO_ROOT_V1,
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    RouteReleaseV1,
    _require_root,
    canonical_global_bytes_v1,
    hash_global_v1,
)
from .zdex_buyback_price_authority_v1 import (
    ZDEXBuybackPriceAuthorityCandidateV1,
    verify_zdex_buyback_price_authority_v1,
)
from .zdex_buyback_price_safety_v1 import (
    ZDEX_BUYBACK_PRICE_SAFETY_POLICY_KIND_V1,
    ZDEXBuybackOraclePriceOccurrenceV1,
    ZDEXBuybackPriceSafetyPolicyV1,
)
from .zdex_fee_allocation_types_v1 import FEE_BUYBACK_PRINCIPAL_V1
from .zdex_purchase_burn_effects_v1 import (
    burn_effects_v1,
    purchase_effects_v1,
    purchase_effects_v2,
)
from .zdex_purchase_burn_route_types_v1 import (
    AMM_PURCHASE_OUTPUT_ROLE_V1,
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    ZDEX_BURN_INPUT_ROLE_V1,
    ZDEX_BUYBACK_EXECUTION_POLICY_KIND_V1,
    ZDEXAMMPurchaseJournalV1,
    ZDEXAMMPurchaseJournalV2,
    ZDEXBurnJournalV1,
    ZDEXBuybackExecutionPolicyV1,
    zdex_amm_purchase_port_schema_root_v1,
    zdex_burn_port_schema_root_v1,
    zdex_occurrence_burn_port_v1,
    zdex_pool_reserve_principal_v1,
)

VERIFIED_ZDEX_AMM_PURCHASE_SCHEMA_V1: Final = "zenodex/verified-zdex-amm-purchase/v1"
VERIFIED_ZDEX_AMM_PURCHASE_SCHEMA_V2: Final = "zenodex/verified-zdex-amm-purchase/v2"
GOVERNED_VERIFIED_ZDEX_AMM_PURCHASE_SCHEMA_V2: Final = (
    "zenodex/governed-verified-zdex-amm-purchase/v2"
)
VERIFIED_ZDEX_BURN_SCHEMA_V1: Final = "zenodex/verified-zdex-burn/v1"
_VERIFIED_PURCHASE_TOKEN = object()
_VERIFIED_PURCHASE_V2_TOKEN = object()
_GOVERNED_VERIFIED_PURCHASE_V2_TOKEN = object()
_VERIFIED_BURN_TOKEN = object()


class ZDEXLaneSuccinctReceiptVerifierV1(Protocol):
    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None: ...


@dataclass(frozen=True, slots=True)
class ZDEXLaneReceiptEnvelopeV1:
    receipt_kind: ReceiptKindV1
    receipt_bytes: bytes

    def __post_init__(self) -> None:
        if type(self.receipt_kind) is not ReceiptKindV1:
            raise TypeError("ZDEX lane receipt kind is not closed")
        if type(self.receipt_bytes) is not bytes:
            raise TypeError("ZDEX lane receipt bytes must be exact bytes")


@dataclass(frozen=True, slots=True)
class ZDEXPurchaseReceiptCandidateV1:
    route_release: RouteReleaseV1
    module_release: LaneModuleReleaseV1
    occurrence: EconomicCommandOccurrenceV1
    journal: ZDEXAMMPurchaseJournalV1
    effects: GlobalEconomicEffectPlanV1
    receipt: ZDEXLaneReceiptEnvelopeV1

    def __post_init__(self) -> None:
        _require_candidate_types(
            self.route_release,
            self.module_release,
            self.occurrence,
            self.journal,
            self.effects,
            self.receipt,
            expected_journal=ZDEXAMMPurchaseJournalV1,
        )


@dataclass(frozen=True, slots=True)
class ZDEXPurchaseReceiptCandidateV2:
    route_release: RouteReleaseV1
    module_release: LaneModuleReleaseV1
    occurrence: EconomicCommandOccurrenceV1
    pre_state: GlobalEconomicStateV1
    execution_policy: ZDEXBuybackExecutionPolicyV1
    price_policy: ZDEXBuybackPriceSafetyPolicyV1
    price_occurrence: ZDEXBuybackOraclePriceOccurrenceV1
    journal: ZDEXAMMPurchaseJournalV2
    effects: GlobalEconomicEffectPlanV1
    receipt: ZDEXLaneReceiptEnvelopeV1

    def __post_init__(self) -> None:
        expected = (
            (self.route_release, RouteReleaseV1, "route release"),
            (self.module_release, LaneModuleReleaseV1, "module release"),
            (self.occurrence, EconomicCommandOccurrenceV1, "occurrence"),
            (self.pre_state, GlobalEconomicStateV1, "pre-state"),
            (self.execution_policy, ZDEXBuybackExecutionPolicyV1, "execution policy"),
            (self.price_policy, ZDEXBuybackPriceSafetyPolicyV1, "price policy"),
            (
                self.price_occurrence,
                ZDEXBuybackOraclePriceOccurrenceV1,
                "price occurrence",
            ),
            (self.journal, ZDEXAMMPurchaseJournalV2, "journal"),
            (self.effects, GlobalEconomicEffectPlanV1, "effects"),
            (self.receipt, ZDEXLaneReceiptEnvelopeV1, "receipt"),
        )
        for value, expected_type, label in expected:
            if type(value) is not expected_type:
                raise TypeError(
                    f"ZDEX purchase V2 receipt {label} must be exact typed data"
                )


@dataclass(frozen=True, slots=True)
class ZDEXBurnReceiptCandidateV1:
    route_release: RouteReleaseV1
    module_release: LaneModuleReleaseV1
    occurrence: EconomicCommandOccurrenceV1
    journal: ZDEXBurnJournalV1
    effects: GlobalEconomicEffectPlanV1
    receipt: ZDEXLaneReceiptEnvelopeV1

    def __post_init__(self) -> None:
        _require_candidate_types(
            self.route_release,
            self.module_release,
            self.occurrence,
            self.journal,
            self.effects,
            self.receipt,
            expected_journal=ZDEXBurnJournalV1,
        )


@dataclass(frozen=True, slots=True)
class _ZDEXPurchaseReceiptSnapshotV1:
    route_release: RouteReleaseV1
    module_release: LaneModuleReleaseV1
    occurrence: EconomicCommandOccurrenceV1
    journal: ZDEXAMMPurchaseJournalV1
    effects: GlobalEconomicEffectPlanV1
    receipt: ZDEXLaneReceiptEnvelopeV1


@dataclass(frozen=True, slots=True)
class _ZDEXPurchaseReceiptSnapshotV2:
    route_release: RouteReleaseV1
    module_release: LaneModuleReleaseV1
    occurrence: EconomicCommandOccurrenceV1
    pre_state: GlobalEconomicStateV1
    execution_policy: ZDEXBuybackExecutionPolicyV1
    price_policy: ZDEXBuybackPriceSafetyPolicyV1
    price_occurrence: ZDEXBuybackOraclePriceOccurrenceV1
    journal: ZDEXAMMPurchaseJournalV2
    effects: GlobalEconomicEffectPlanV1
    receipt: ZDEXLaneReceiptEnvelopeV1


@dataclass(frozen=True, slots=True)
class _ZDEXBurnReceiptSnapshotV1:
    route_release: RouteReleaseV1
    module_release: LaneModuleReleaseV1
    occurrence: EconomicCommandOccurrenceV1
    journal: ZDEXBurnJournalV1
    effects: GlobalEconomicEffectPlanV1
    receipt: ZDEXLaneReceiptEnvelopeV1


def _require_candidate_types(
    route_release: object,
    module_release: object,
    occurrence: object,
    journal: object,
    effects: object,
    receipt: object,
    *,
    expected_journal: type[object],
) -> None:
    expected = (
        (route_release, RouteReleaseV1, "route release"),
        (module_release, LaneModuleReleaseV1, "module release"),
        (occurrence, EconomicCommandOccurrenceV1, "occurrence"),
        (journal, expected_journal, "journal"),
        (effects, GlobalEconomicEffectPlanV1, "effects"),
        (receipt, ZDEXLaneReceiptEnvelopeV1, "receipt"),
    )
    for value, expected_type, label in expected:
        if type(value) is not expected_type:
            raise TypeError(f"ZDEX lane receipt {label} must be exact typed data")


def _snapshot_purchase_journal_v1(
    journal: ZDEXAMMPurchaseJournalV1,
) -> ZDEXAMMPurchaseJournalV1:
    if type(journal) is not ZDEXAMMPurchaseJournalV1:
        raise TypeError("ZDEX purchase journal must be exact typed data")
    _require_exact_dataclass_scalars_v1(journal, name="ZDEX purchase journal")
    return replace(journal)


def _snapshot_purchase_journal_v2(
    journal: ZDEXAMMPurchaseJournalV2,
) -> ZDEXAMMPurchaseJournalV2:
    if type(journal) is not ZDEXAMMPurchaseJournalV2:
        raise TypeError("ZDEX purchase V2 journal must be exact typed data")
    _require_exact_dataclass_scalars_v1(journal, name="ZDEX purchase V2 journal")
    journal.validate()
    return replace(journal)


def _snapshot_burn_journal_v1(journal: ZDEXBurnJournalV1) -> ZDEXBurnJournalV1:
    if type(journal) is not ZDEXBurnJournalV1:
        raise TypeError("ZDEX burn journal must be exact typed data")
    _require_exact_dataclass_scalars_v1(journal, name="ZDEX burn journal")
    return replace(journal)


def _snapshot_purchase_candidate_v1(
    candidate: ZDEXPurchaseReceiptCandidateV1,
) -> _ZDEXPurchaseReceiptSnapshotV1:
    """Own and revalidate every purchase value read across the callback."""

    if type(candidate) is not ZDEXPurchaseReceiptCandidateV1:
        raise TypeError("ZDEX purchase receipt candidate must be exact typed data")
    candidate.__post_init__()
    return _ZDEXPurchaseReceiptSnapshotV1(
        route_release=_snapshot_route_release_v1(candidate.route_release),
        module_release=_snapshot_lane_release_v1(candidate.module_release),
        occurrence=_snapshot_occurrence_v1(candidate.occurrence),
        journal=_snapshot_purchase_journal_v1(candidate.journal),
        effects=_snapshot_effect_plan_v1(candidate.effects),
        receipt=ZDEXLaneReceiptEnvelopeV1(
            candidate.receipt.receipt_kind,
            candidate.receipt.receipt_bytes,
        ),
    )


def _snapshot_purchase_candidate_v2(
    candidate: ZDEXPurchaseReceiptCandidateV2,
) -> _ZDEXPurchaseReceiptSnapshotV2:
    """Own and revalidate every authority-bound purchase input."""

    if type(candidate) is not ZDEXPurchaseReceiptCandidateV2:
        raise TypeError("ZDEX purchase V2 receipt candidate must be exact typed data")
    candidate.__post_init__()
    for value, name in (
        (candidate.execution_policy, "execution policy"),
        (candidate.price_policy, "price policy"),
        (candidate.price_occurrence, "price occurrence"),
    ):
        _require_exact_dataclass_scalars_v1(
            value,
            name=f"ZDEX purchase V2 {name}",
        )
    return _ZDEXPurchaseReceiptSnapshotV2(
        route_release=_snapshot_route_release_v1(candidate.route_release),
        module_release=_snapshot_lane_release_v1(candidate.module_release),
        occurrence=_snapshot_occurrence_v1(candidate.occurrence),
        pre_state=_snapshot_state_v1(candidate.pre_state),
        execution_policy=replace(candidate.execution_policy),
        price_policy=replace(candidate.price_policy),
        price_occurrence=replace(candidate.price_occurrence),
        journal=_snapshot_purchase_journal_v2(candidate.journal),
        effects=_snapshot_effect_plan_v1(candidate.effects),
        receipt=ZDEXLaneReceiptEnvelopeV1(
            candidate.receipt.receipt_kind,
            candidate.receipt.receipt_bytes,
        ),
    )


def _snapshot_burn_candidate_v1(
    candidate: ZDEXBurnReceiptCandidateV1,
) -> _ZDEXBurnReceiptSnapshotV1:
    """Own and revalidate every burn value read across the callback."""

    if type(candidate) is not ZDEXBurnReceiptCandidateV1:
        raise TypeError("ZDEX burn receipt candidate must be exact typed data")
    candidate.__post_init__()
    return _ZDEXBurnReceiptSnapshotV1(
        route_release=_snapshot_route_release_v1(candidate.route_release),
        module_release=_snapshot_lane_release_v1(candidate.module_release),
        occurrence=_snapshot_occurrence_v1(candidate.occurrence),
        journal=_snapshot_burn_journal_v1(candidate.journal),
        effects=_snapshot_effect_plan_v1(candidate.effects),
        receipt=ZDEXLaneReceiptEnvelopeV1(
            candidate.receipt.receipt_kind,
            candidate.receipt.receipt_bytes,
        ),
    )


@dataclass(frozen=True, slots=True)
class _VerifiedZDEXLaneFieldsV1:
    route_release_id: str
    module_release_id: str
    command_occurrence_id: str
    profile_root: str
    writer_epoch: int
    journal_root: str
    journal_digest: str
    effect_plan_root: str
    expected_image_id: str
    receipt_digest: str
    receipt_kind: ReceiptKindV1
    authority_head_root: str
    verifier_binding_root: str
    price_authority_root: str = ZERO_ROOT_V1
    price_safety_policy_root: str = ZERO_ROOT_V1


class _VerifiedZDEXLaneV1:
    __slots__ = ("_fields",)
    _fields: _VerifiedZDEXLaneFieldsV1
    _token: object
    _schema: str
    _domain: str

    def __init__(self, token: object, fields: _VerifiedZDEXLaneFieldsV1) -> None:
        if token is not self._token:
            raise TypeError(f"{type(self).__name__} is verifier-constructed")
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError(f"{type(self).__name__} is immutable")

    @property
    def route_release_id(self) -> str:
        return self._fields.route_release_id

    @property
    def module_release_id(self) -> str:
        return self._fields.module_release_id

    @property
    def command_occurrence_id(self) -> str:
        return self._fields.command_occurrence_id

    @property
    def profile_root(self) -> str:
        return self._fields.profile_root

    @property
    def writer_epoch(self) -> int:
        return self._fields.writer_epoch

    @property
    def journal_root(self) -> str:
        return self._fields.journal_root

    @property
    def journal_digest(self) -> str:
        return self._fields.journal_digest

    @property
    def effect_plan_root(self) -> str:
        return self._fields.effect_plan_root

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
    def authority_head_root(self) -> str:
        return self._fields.authority_head_root

    @property
    def verifier_binding_root(self) -> str:
        return self._fields.verifier_binding_root

    @property
    def price_authority_root(self) -> str:
        return self._fields.price_authority_root

    @property
    def price_safety_policy_root(self) -> str:
        return self._fields.price_safety_policy_root

    def _leaf_binding_body(self) -> dict[str, object]:
        return {
            "schema": self._schema,
            "route_release_id": self.route_release_id,
            "module_release_id": self.module_release_id,
            "command_occurrence_id": self.command_occurrence_id,
            "profile_root": self.profile_root,
            "writer_epoch": self.writer_epoch,
            "journal_root": self.journal_root,
            "journal_digest": self.journal_digest,
            "effect_plan_root": self.effect_plan_root,
            "expected_image_id": self.expected_image_id,
            "receipt_digest": self.receipt_digest,
            "receipt_kind": self.receipt_kind,
        }

    @property
    def leaf_binding_root(self) -> str:
        """Return the cross-language leaf root without host authority metadata."""

        return hash_global_v1(self._domain, self._leaf_binding_body())

    @property
    def binding_root(self) -> str:
        body = self._leaf_binding_body()
        if self.authority_head_root != ZERO_ROOT_V1 or self.verifier_binding_root != ZERO_ROOT_V1:
            body.update(
                authority_head_root=self.authority_head_root,
                verifier_binding_root=self.verifier_binding_root,
            )
        return hash_global_v1(self._domain, body)


class VerifiedZDEXAMMPurchaseV1(_VerifiedZDEXLaneV1):
    _token = _VERIFIED_PURCHASE_TOKEN
    _schema = VERIFIED_ZDEX_AMM_PURCHASE_SCHEMA_V1
    _domain = "verified-zdex-amm-purchase-v1"


class VerifiedZDEXAMMPurchaseV2(_VerifiedZDEXLaneV1):
    _token = _VERIFIED_PURCHASE_V2_TOKEN
    _schema = VERIFIED_ZDEX_AMM_PURCHASE_SCHEMA_V2
    _domain = "verified-zdex-amm-purchase-v2"

    @property
    def leaf_binding_root(self) -> str:
        if (
            self.price_authority_root == ZERO_ROOT_V1
            or self.price_safety_policy_root == ZERO_ROOT_V1
        ):
            raise ValueError("ZDEX purchase V2 price authority is absent")
        body: dict[str, object] = {
            "schema": self._schema,
            "route_release_id": self.route_release_id,
            "module_release_id": self.module_release_id,
            "command_occurrence_id": self.command_occurrence_id,
            "profile_root": self.profile_root,
            "writer_epoch": self.writer_epoch,
            "journal_root": self.journal_root,
            "journal_digest": self.journal_digest,
            "effect_plan_root": self.effect_plan_root,
            "expected_image_id": self.expected_image_id,
            "receipt_digest": self.receipt_digest,
            "receipt_kind": self.receipt_kind,
            "price_authority_root": self.price_authority_root,
            "price_safety_policy_root": self.price_safety_policy_root,
        }
        return hash_global_v1(self._domain, body)

    @property
    def binding_root(self) -> str:
        return self.leaf_binding_root


@dataclass(frozen=True, slots=True)
class _GovernedVerifiedZDEXAMMPurchaseFieldsV2:
    verified_leaf: VerifiedZDEXAMMPurchaseV2
    authority_head_root: str
    verifier_binding_root: str
    policy_registry_root: str


class GovernedVerifiedZDEXAMMPurchaseV2:
    """Opaque current-authority admission of one canonical V2 leaf."""

    __slots__ = ("_fields",)
    _fields: _GovernedVerifiedZDEXAMMPurchaseFieldsV2

    def __init__(
        self,
        token: object,
        fields: _GovernedVerifiedZDEXAMMPurchaseFieldsV2,
    ) -> None:
        if token is not _GOVERNED_VERIFIED_PURCHASE_V2_TOKEN:
            raise TypeError("governed ZDEX purchase V2 is verifier-constructed")
        if type(fields) is not _GovernedVerifiedZDEXAMMPurchaseFieldsV2:
            raise TypeError("governed ZDEX purchase V2 fields are not closed")
        if type(fields.verified_leaf) is not VerifiedZDEXAMMPurchaseV2:
            raise TypeError("governed ZDEX purchase V2 leaf is not closed")
        for value, name in (
            (fields.authority_head_root, "authority head"),
            (fields.verifier_binding_root, "verifier binding"),
            (fields.policy_registry_root, "policy registry"),
        ):
            if type(value) is not str:
                raise TypeError(f"governed ZDEX purchase V2 {name} root must be exact str")
            _require_root(value, name=f"governed ZDEX purchase V2 {name} root")
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("governed ZDEX purchase V2 is immutable")

    @property
    def verified_leaf(self) -> VerifiedZDEXAMMPurchaseV2:
        return self._fields.verified_leaf

    @property
    def authority_head_root(self) -> str:
        return self._fields.authority_head_root

    @property
    def verifier_binding_root(self) -> str:
        return self._fields.verifier_binding_root

    @property
    def policy_registry_root(self) -> str:
        return self._fields.policy_registry_root

    @property
    def price_authority_root(self) -> str:
        return self.verified_leaf.price_authority_root

    @property
    def price_safety_policy_root(self) -> str:
        return self.verified_leaf.price_safety_policy_root

    @property
    def leaf_binding_root(self) -> str:
        return self.verified_leaf.leaf_binding_root

    @property
    def binding_root(self) -> str:
        return hash_global_v1(
            "governed-verified-zdex-amm-purchase-v2",
            {
                "schema": GOVERNED_VERIFIED_ZDEX_AMM_PURCHASE_SCHEMA_V2,
                "leaf_binding_root": self.leaf_binding_root,
                "authority_head_root": self.authority_head_root,
                "verifier_binding_root": self.verifier_binding_root,
                "policy_registry_root": self.policy_registry_root,
            },
        )


class VerifiedZDEXBurnV1(_VerifiedZDEXLaneV1):
    _token = _VERIFIED_BURN_TOKEN
    _schema = VERIFIED_ZDEX_BURN_SCHEMA_V1
    _domain = "verified-zdex-burn-v1"


def _require_route_shape(route: RouteReleaseV1) -> None:
    if route.status is not ReleaseStatusV1.SHADOW:
        raise ValueError("ZDEX purchase-burn route release must remain SHADOW")
    if route.command_kind != PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1:
        raise ValueError("ZDEX purchase-burn route command mismatch")
    if route.ordered_lanes != (LaneIdV1.SPOT_LIQUIDITY, LaneIdV1.ZDEX_TOKENOMICS):
        raise ValueError("ZDEX purchase-burn route lane order mismatch")
    if route.dependency_roles != (AMM_PURCHASE_OUTPUT_ROLE_V1, ZDEX_BURN_INPUT_ROLE_V1):
        raise ValueError("ZDEX purchase-burn dependency roles mismatch")
    expected_ports = (
        zdex_amm_purchase_port_schema_root_v1(),
        zdex_burn_port_schema_root_v1(),
    )
    if route.port_schema_roots != expected_ports:
        raise ValueError("ZDEX purchase-burn port schemas mismatch")


def _require_release_and_occurrence(
    route: RouteReleaseV1,
    release: LaneModuleReleaseV1,
    occurrence: EconomicCommandOccurrenceV1,
    *,
    lane_id: LaneIdV1,
    route_index: int,
) -> None:
    _require_route_shape(route)
    if release.status is not ReleaseStatusV1.SHADOW:
        raise ValueError("ZDEX lane module release must remain SHADOW")
    if release.lane_id is not lane_id:
        raise ValueError("ZDEX lane module release lane mismatch")
    if route.module_release_ids[route_index] != release.release_id:
        raise ValueError("ZDEX route module release mismatch")
    if PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1 not in release.command_variants:
        raise ValueError("ZDEX lane release lacks the purchase-burn command")
    if (
        occurrence.command_kind != route.command_kind
        or occurrence.route_release_id != route.route_release_id
    ):
        raise ValueError("ZDEX purchase-burn occurrence route mismatch")


def _receipt_digests(
    journal: object,
    receipt: ZDEXLaneReceiptEnvelopeV1,
) -> tuple[bytes, str, str]:
    if receipt.receipt_kind is not ReceiptKindV1.SUCCINCT:
        raise ValueError("ZDEX lane verification requires a succinct receipt")
    if not receipt.receipt_bytes:
        raise ValueError("ZDEX lane receipt bytes must be nonempty")
    journal_bytes = canonical_global_bytes_v1(journal)
    return (
        journal_bytes,
        "0x" + hashlib.sha256(journal_bytes).hexdigest(),
        "0x" + hashlib.sha256(receipt.receipt_bytes).hexdigest(),
    )


def verify_zdex_amm_purchase_receipt_v1(
    candidate: ZDEXPurchaseReceiptCandidateV1,
    receipt_verifier: ZDEXLaneSuccinctReceiptVerifierV1,
) -> VerifiedZDEXAMMPurchaseV1:
    """Authenticate exact AMM output under its release-selected shadow image."""

    owned = _snapshot_purchase_candidate_v1(candidate)
    _require_release_and_occurrence(
        owned.route_release,
        owned.module_release,
        owned.occurrence,
        lane_id=LaneIdV1.SPOT_LIQUIDITY,
        route_index=0,
    )
    journal = owned.journal
    occurrence = owned.occurrence
    bindings = (
        (journal.chain_id, occurrence.chain_id, "chain"),
        (journal.deployment_root, occurrence.deployment_root, "deployment"),
        (journal.profile_root, occurrence.profile_root, "profile"),
        (journal.route_release_id, owned.route_release.route_release_id, "route"),
        (journal.command_occurrence_id, occurrence.occurrence_id, "occurrence"),
        (journal.spot_module_release_id, owned.module_release.release_id, "module release"),
        (
            journal.issue_burn_policy_root,
            owned.route_release.issue_burn_policy_root,
            "issue/burn policy",
        ),
        (journal.effect_plan_root, owned.effects.effect_plan_root, "effect plan"),
    )
    for actual, expected, label in bindings:
        if actual != expected:
            raise ValueError(f"ZDEX purchase {label} mismatch")
    if owned.effects != purchase_effects_v1(journal):
        raise ValueError("ZDEX purchase effect rows or conservation mismatch")
    journal_bytes, journal_digest, receipt_digest = _receipt_digests(
        journal,
        owned.receipt,
    )
    if len(journal_bytes) > owned.module_release.max_journal_bytes:
        raise ValueError("ZDEX purchase journal exceeds release byte ceiling")
    receipt_verifier.verify_succinct_receipt(
        owned.receipt.receipt_bytes,
        expected_image_id=owned.module_release.guest_image_id,
        expected_journal_bytes=journal_bytes,
    )
    return VerifiedZDEXAMMPurchaseV1(
        _VERIFIED_PURCHASE_TOKEN,
        _VerifiedZDEXLaneFieldsV1(
            owned.route_release.route_release_id,
            owned.module_release.release_id,
            occurrence.occurrence_id,
            occurrence.profile_root,
            journal.writer_epoch,
            journal.journal_root,
            journal_digest,
            owned.effects.effect_plan_root,
            owned.module_release.guest_image_id,
            receipt_digest,
            owned.receipt.receipt_kind,
            ZERO_ROOT_V1,
            ZERO_ROOT_V1,
        ),
    )


def verify_zdex_amm_purchase_receipt_v2(
    candidate: ZDEXPurchaseReceiptCandidateV2,
    receipt_verifier: ZDEXLaneSuccinctReceiptVerifierV1,
) -> VerifiedZDEXAMMPurchaseV2:
    """Authenticate a purchase whose price inputs have committed authority."""

    owned = _snapshot_purchase_candidate_v2(candidate)
    _require_release_and_occurrence(
        owned.route_release,
        owned.module_release,
        owned.occurrence,
        lane_id=LaneIdV1.SPOT_LIQUIDITY,
        route_index=0,
    )
    journal = owned.journal
    occurrence = owned.occurrence
    execution_policy_root = owned.execution_policy.policy_root
    price_policy_root = owned.price_policy.policy_root
    price_occurrence_root = owned.price_occurrence.occurrence_root
    expected_quote_pool = zdex_pool_reserve_principal_v1(
        pool_id=owned.execution_policy.pool_id,
        asset_id=owned.execution_policy.quote_asset_id,
    )
    expected_zdex_pool = zdex_pool_reserve_principal_v1(
        pool_id=owned.execution_policy.pool_id,
        asset_id=owned.execution_policy.zdex_asset_id,
    )
    expected_burn_bucket = zdex_occurrence_burn_port_v1(
        profile_root=occurrence.profile_root,
        route_release_id=owned.route_release.route_release_id,
        command_occurrence_id=occurrence.occurrence_id,
    )
    if any(
        (
            journal.chain_id != occurrence.chain_id,
            journal.deployment_root != occurrence.deployment_root,
            journal.profile_root != occurrence.profile_root,
            journal.route_release_id != owned.route_release.route_release_id,
            journal.command_occurrence_id != occurrence.occurrence_id,
            journal.spot_module_release_id != owned.module_release.release_id,
            journal.issue_burn_policy_root
            != owned.route_release.issue_burn_policy_root,
            journal.buyback_execution_policy_root != execution_policy_root,
            journal.price_safety_policy_root != price_policy_root,
            journal.oracle_occurrence_root != price_occurrence_root,
            journal.oracle_observed_height
            != owned.price_occurrence.observed_height,
            journal.oracle_quote_numerator_atoms
            != owned.price_occurrence.quote_numerator_atoms,
            journal.oracle_zdex_denominator_atoms
            != owned.price_occurrence.zdex_denominator_atoms,
            journal.quote_asset_id != owned.execution_policy.quote_asset_id,
            journal.zdex_asset_id != owned.execution_policy.zdex_asset_id,
            journal.quote_source_bucket_id != FEE_BUYBACK_PRINCIPAL_V1,
            journal.quote_pool_bucket_id != expected_quote_pool,
            journal.zdex_pool_bucket_id != expected_zdex_pool,
            journal.burn_bucket_id != expected_burn_bucket,
            journal.effect_plan_root != owned.effects.effect_plan_root,
            owned.effects != purchase_effects_v2(journal),
        )
    ):
        raise ValueError("ZDEX purchase V2 journal or effects mismatch")
    price_authority = verify_zdex_buyback_price_authority_v1(
        ZDEXBuybackPriceAuthorityCandidateV1(
            pre_state=owned.pre_state,
            route=owned.route_release,
            occurrence=occurrence,
            execution_policy=owned.execution_policy,
            price_policy=owned.price_policy,
            price_occurrence=owned.price_occurrence,
            route_safe_quote_limit_atoms=journal.route_safe_quote_limit_atoms,
            minimum_output_atoms=journal.minimum_output_atoms,
            expected_quote_reserve_atoms=journal.quote_pool_pre_atoms,
            expected_zdex_reserve_atoms=journal.zdex_pool_pre_atoms,
            quote_amount_in_atoms=journal.quote_amount_in_atoms,
            purchased_zdex_atoms=journal.purchased_zdex_atoms,
        )
    )
    journal_bytes, journal_digest, receipt_digest = _receipt_digests(
        journal,
        owned.receipt,
    )
    if len(journal_bytes) > owned.module_release.max_journal_bytes:
        raise ValueError("ZDEX purchase V2 journal exceeds release byte ceiling")
    receipt_verifier.verify_succinct_receipt(
        owned.receipt.receipt_bytes,
        expected_image_id=owned.module_release.guest_image_id,
        expected_journal_bytes=journal_bytes,
    )
    return VerifiedZDEXAMMPurchaseV2(
        _VERIFIED_PURCHASE_V2_TOKEN,
        _VerifiedZDEXLaneFieldsV1(
            route_release_id=owned.route_release.route_release_id,
            module_release_id=owned.module_release.release_id,
            command_occurrence_id=occurrence.occurrence_id,
            profile_root=occurrence.profile_root,
            writer_epoch=journal.writer_epoch,
            journal_root=journal.journal_root,
            journal_digest=journal_digest,
            effect_plan_root=owned.effects.effect_plan_root,
            expected_image_id=owned.module_release.guest_image_id,
            receipt_digest=receipt_digest,
            receipt_kind=owned.receipt.receipt_kind,
            authority_head_root=ZERO_ROOT_V1,
            verifier_binding_root=ZERO_ROOT_V1,
            price_authority_root=price_authority.authority_root,
            price_safety_policy_root=price_policy_root,
        ),
    )


def verify_zdex_burn_receipt_v1(
    candidate: ZDEXBurnReceiptCandidateV1,
    receipt_verifier: ZDEXLaneSuccinctReceiptVerifierV1,
) -> VerifiedZDEXBurnV1:
    """Authenticate exact burn output under its release-selected shadow image."""

    owned = _snapshot_burn_candidate_v1(candidate)
    _require_release_and_occurrence(
        owned.route_release,
        owned.module_release,
        owned.occurrence,
        lane_id=LaneIdV1.ZDEX_TOKENOMICS,
        route_index=1,
    )
    journal = owned.journal
    occurrence = owned.occurrence
    bindings = (
        (journal.chain_id, occurrence.chain_id, "chain"),
        (journal.deployment_root, occurrence.deployment_root, "deployment"),
        (journal.profile_root, occurrence.profile_root, "profile"),
        (journal.route_release_id, owned.route_release.route_release_id, "route"),
        (journal.command_occurrence_id, occurrence.occurrence_id, "occurrence"),
        (
            journal.tokenomics_module_release_id,
            owned.module_release.release_id,
            "module release",
        ),
        (
            journal.issue_burn_policy_root,
            owned.route_release.issue_burn_policy_root,
            "issue/burn policy",
        ),
        (journal.effect_plan_root, owned.effects.effect_plan_root, "effect plan"),
    )
    for actual, expected, label in bindings:
        if actual != expected:
            raise ValueError(f"ZDEX burn {label} mismatch")
    if owned.effects != burn_effects_v1(journal):
        raise ValueError("ZDEX burn effect rows or conservation mismatch")
    journal_bytes, journal_digest, receipt_digest = _receipt_digests(
        journal,
        owned.receipt,
    )
    if len(journal_bytes) > owned.module_release.max_journal_bytes:
        raise ValueError("ZDEX burn journal exceeds release byte ceiling")
    receipt_verifier.verify_succinct_receipt(
        owned.receipt.receipt_bytes,
        expected_image_id=owned.module_release.guest_image_id,
        expected_journal_bytes=journal_bytes,
    )
    return VerifiedZDEXBurnV1(
        _VERIFIED_BURN_TOKEN,
        _VerifiedZDEXLaneFieldsV1(
            owned.route_release.route_release_id,
            owned.module_release.release_id,
            occurrence.occurrence_id,
            occurrence.profile_root,
            journal.writer_epoch,
            journal.journal_root,
            journal_digest,
            owned.effects.effect_plan_root,
            owned.module_release.guest_image_id,
            receipt_digest,
            owned.receipt.receipt_kind,
            ZERO_ROOT_V1,
            ZERO_ROOT_V1,
        ),
    )


class _ProfileLaneReceiptVerifierV1:
    """Narrow adapter that removes caller-selected lane image authority."""

    __slots__ = ("_bound", "_profile", "_lane_id", "_module_release_id")

    def __init__(
        self,
        bound: BoundEconomicReceiptVerifierV1,
        profile: EconomicProfileSnapshotV1,
        lane_id: LaneIdV1,
        module_release_id: str,
    ) -> None:
        self._bound = bound
        self._profile = profile
        self._lane_id = lane_id
        self._module_release_id = module_release_id

    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None:
        self._bound.verify_profile_lane_receipt(
            receipt_bytes,
            profile=self._profile,
            lane_id=self._lane_id,
            expected_module_release_id=self._module_release_id,
            expected_image_id=expected_image_id,
            expected_journal_bytes=expected_journal_bytes,
        )


def _require_current_shadow_authority_v1(
    *,
    profile: EconomicProfileSnapshotV1,
    route: RouteReleaseV1,
    release: LaneModuleReleaseV1,
    occurrence: EconomicCommandOccurrenceV1,
    lane_id: LaneIdV1,
    authority_head: GlobalEconomicAuthorityHeadV1,
    receipt_verifier: BoundEconomicReceiptVerifierV1,
) -> EconomicProfileSnapshotV1:
    if type(authority_head) is not GlobalEconomicAuthorityHeadV1:
        raise TypeError("ZDEX governed receipt authority head must be exact typed data")
    if type(receipt_verifier) is not BoundEconomicReceiptVerifierV1:
        raise TypeError("ZDEX governed receipt verifier must be a bound capability")
    owned_profile = snapshot_economic_profile_v1(profile)
    governed_release = owned_profile.lane_registry.release_for(lane_id)
    governed_routes = tuple(
        item
        for item in owned_profile.route_registry.routes
        if item.command_kind == occurrence.command_kind
    )
    if (
        owned_profile.status is not ProfileStatusV1.SHADOW
        or len(governed_routes) != 1
        or governed_routes[0] != route
        or governed_release != release
        or authority_head.status is not GlobalEconomicAuthorityStatusV1.ACTIVE
        or authority_head.chain_id != occurrence.chain_id
        or authority_head.deployment_root != occurrence.deployment_root
        or occurrence.profile_root != owned_profile.profile_id
        or authority_head.profile_root != owned_profile.profile_id
        or authority_head.writer_epoch != owned_profile.authority_epoch
        or authority_head.verifier_registry_root != owned_profile.verifier_registry_root
        or authority_head.verifier_release_id != receipt_verifier.release_id
        or authority_head.verifier_binding_root != receipt_verifier.binding_root
        or authority_head.root_image_id != owned_profile.root_image_id
    ):
        raise ValueError("ZDEX lane receipt is outside the current governed authority")
    receipt_verifier.require_binding(
        verifier_registry_root=authority_head.verifier_registry_root,
        deployment_root=authority_head.deployment_root,
        profile_root=authority_head.profile_root,
        root_image_id=authority_head.root_image_id,
        selection_purpose=EconomicReceiptVerifierSelectionPurposeV1.RESEARCH_SHADOW,
    )
    return owned_profile


def verify_governed_zdex_amm_purchase_receipt_shadow_v1(
    candidate: ZDEXPurchaseReceiptCandidateV1,
    *,
    profile: EconomicProfileSnapshotV1,
    authority_head: GlobalEconomicAuthorityHeadV1,
    receipt_verifier: BoundEconomicReceiptVerifierV1,
) -> VerifiedZDEXAMMPurchaseV1:
    """Verify a purchase under the current profile-selected Spot image."""

    owned = _snapshot_purchase_candidate_v1(candidate)
    owned_profile = _require_current_shadow_authority_v1(
        profile=profile,
        route=owned.route_release,
        release=owned.module_release,
        occurrence=owned.occurrence,
        lane_id=LaneIdV1.SPOT_LIQUIDITY,
        authority_head=authority_head,
        receipt_verifier=receipt_verifier,
    )
    if owned.journal.writer_epoch != owned_profile.authority_epoch:
        raise ValueError("ZDEX purchase receipt writer epoch is outside the profile")
    verified = verify_zdex_amm_purchase_receipt_v1(
        ZDEXPurchaseReceiptCandidateV1(
            owned.route_release,
            owned.module_release,
            owned.occurrence,
            owned.journal,
            owned.effects,
            owned.receipt,
        ),
        _ProfileLaneReceiptVerifierV1(
            receipt_verifier,
            owned_profile,
            LaneIdV1.SPOT_LIQUIDITY,
            owned.module_release.release_id,
        ),
    )
    return VerifiedZDEXAMMPurchaseV1(
        _VERIFIED_PURCHASE_TOKEN,
        replace(
            verified._fields,
            authority_head_root=authority_head.authority_root,
            verifier_binding_root=receipt_verifier.binding_root,
        ),
    )


def verify_governed_zdex_amm_purchase_receipt_shadow_v2(
    candidate: ZDEXPurchaseReceiptCandidateV2,
    *,
    profile: EconomicProfileSnapshotV1,
    policy_registry: EconomicPolicyRegistryV1,
    authority_head: GlobalEconomicAuthorityHeadV1,
    receipt_verifier: BoundEconomicReceiptVerifierV1,
) -> GovernedVerifiedZDEXAMMPurchaseV2:
    """Verify an authority-bound purchase under the selected Spot image."""

    owned = _snapshot_purchase_candidate_v2(candidate)
    owned_profile = _require_current_shadow_authority_v1(
        profile=profile,
        route=owned.route_release,
        release=owned.module_release,
        occurrence=owned.occurrence,
        lane_id=LaneIdV1.SPOT_LIQUIDITY,
        authority_head=authority_head,
        receipt_verifier=receipt_verifier,
    )
    owned_policy_registry = snapshot_economic_policy_registry_v1(policy_registry)
    if owned_policy_registry.registry_root != owned_profile.policy_registry_root:
        raise ValueError("ZDEX purchase V2 economic policy registry mismatch")
    execution_binding = owned_policy_registry.require_binding(
        policy_kind=ZDEX_BUYBACK_EXECUTION_POLICY_KIND_V1,
        command_kind=PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    )
    price_binding = owned_policy_registry.require_binding(
        policy_kind=ZDEX_BUYBACK_PRICE_SAFETY_POLICY_KIND_V1,
        command_kind=PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    )
    if execution_binding.policy_root != owned.execution_policy.policy_root:
        raise ValueError("ZDEX purchase V2 execution policy binding mismatch")
    if price_binding.policy_root != owned.price_policy.policy_root:
        raise ValueError("ZDEX purchase V2 price policy binding mismatch")
    if owned.journal.writer_epoch != owned_profile.authority_epoch:
        raise ValueError("ZDEX purchase V2 receipt writer epoch is outside the profile")
    verified = verify_zdex_amm_purchase_receipt_v2(
        ZDEXPurchaseReceiptCandidateV2(
            route_release=owned.route_release,
            module_release=owned.module_release,
            occurrence=owned.occurrence,
            pre_state=owned.pre_state,
            execution_policy=owned.execution_policy,
            price_policy=owned.price_policy,
            price_occurrence=owned.price_occurrence,
            journal=owned.journal,
            effects=owned.effects,
            receipt=owned.receipt,
        ),
        _ProfileLaneReceiptVerifierV1(
            receipt_verifier,
            owned_profile,
            LaneIdV1.SPOT_LIQUIDITY,
            owned.module_release.release_id,
        ),
    )
    return GovernedVerifiedZDEXAMMPurchaseV2(
        _GOVERNED_VERIFIED_PURCHASE_V2_TOKEN,
        _GovernedVerifiedZDEXAMMPurchaseFieldsV2(
            verified_leaf=verified,
            authority_head_root=authority_head.authority_root,
            verifier_binding_root=receipt_verifier.binding_root,
            policy_registry_root=owned_policy_registry.registry_root,
        ),
    )


def verify_governed_zdex_burn_receipt_shadow_v1(
    candidate: ZDEXBurnReceiptCandidateV1,
    *,
    profile: EconomicProfileSnapshotV1,
    authority_head: GlobalEconomicAuthorityHeadV1,
    receipt_verifier: BoundEconomicReceiptVerifierV1,
) -> VerifiedZDEXBurnV1:
    """Verify a burn under the current profile-selected tokenomics image."""

    owned = _snapshot_burn_candidate_v1(candidate)
    owned_profile = _require_current_shadow_authority_v1(
        profile=profile,
        route=owned.route_release,
        release=owned.module_release,
        occurrence=owned.occurrence,
        lane_id=LaneIdV1.ZDEX_TOKENOMICS,
        authority_head=authority_head,
        receipt_verifier=receipt_verifier,
    )
    if owned.journal.writer_epoch != owned_profile.authority_epoch:
        raise ValueError("ZDEX burn receipt writer epoch is outside the profile")
    verified = verify_zdex_burn_receipt_v1(
        ZDEXBurnReceiptCandidateV1(
            owned.route_release,
            owned.module_release,
            owned.occurrence,
            owned.journal,
            owned.effects,
            owned.receipt,
        ),
        _ProfileLaneReceiptVerifierV1(
            receipt_verifier,
            owned_profile,
            LaneIdV1.ZDEX_TOKENOMICS,
            owned.module_release.release_id,
        ),
    )
    return VerifiedZDEXBurnV1(
        _VERIFIED_BURN_TOKEN,
        replace(
            verified._fields,
            authority_head_root=authority_head.authority_root,
            verifier_binding_root=receipt_verifier.binding_root,
        ),
    )


__all__ = [
    "GOVERNED_VERIFIED_ZDEX_AMM_PURCHASE_SCHEMA_V2",
    "VERIFIED_ZDEX_AMM_PURCHASE_SCHEMA_V1",
    "VERIFIED_ZDEX_AMM_PURCHASE_SCHEMA_V2",
    "VERIFIED_ZDEX_BURN_SCHEMA_V1",
    "VerifiedZDEXAMMPurchaseV1",
    "VerifiedZDEXAMMPurchaseV2",
    "GovernedVerifiedZDEXAMMPurchaseV2",
    "VerifiedZDEXBurnV1",
    "ZDEXBurnReceiptCandidateV1",
    "ZDEXLaneReceiptEnvelopeV1",
    "ZDEXLaneSuccinctReceiptVerifierV1",
    "ZDEXPurchaseReceiptCandidateV1",
    "ZDEXPurchaseReceiptCandidateV2",
    "verify_zdex_amm_purchase_receipt_v1",
    "verify_zdex_amm_purchase_receipt_v2",
    "verify_zdex_burn_receipt_v1",
    "verify_governed_zdex_amm_purchase_receipt_shadow_v1",
    "verify_governed_zdex_amm_purchase_receipt_shadow_v2",
    "verify_governed_zdex_burn_receipt_shadow_v1",
]
