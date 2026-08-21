"""Receipt admission for the two leaf outputs of ZDEX purchase-to-burn."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Final, Protocol

from .global_economic_proof_v1 import EconomicCommandOccurrenceV1, ReceiptKindV1
from .global_settlement_types_v1 import (
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    ReleaseStatusV1,
    RouteReleaseV1,
    canonical_global_bytes_v1,
    hash_global_v1,
)
from .zdex_purchase_burn_effects_v1 import burn_effects_v1, purchase_effects_v1
from .zdex_purchase_burn_route_types_v1 import (
    AMM_PURCHASE_OUTPUT_ROLE_V1,
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    ZDEX_BURN_INPUT_ROLE_V1,
    ZDEXAMMPurchaseJournalV1,
    ZDEXBurnJournalV1,
    zdex_amm_purchase_port_schema_root_v1,
    zdex_burn_port_schema_root_v1,
)

VERIFIED_ZDEX_AMM_PURCHASE_SCHEMA_V1: Final = "zenodex/verified-zdex-amm-purchase/v1"
VERIFIED_ZDEX_BURN_SCHEMA_V1: Final = "zenodex/verified-zdex-burn/v1"
_VERIFIED_PURCHASE_TOKEN = object()
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
    def binding_root(self) -> str:
        return hash_global_v1(
            self._domain,
            {
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
            },
        )


class VerifiedZDEXAMMPurchaseV1(_VerifiedZDEXLaneV1):
    _token = _VERIFIED_PURCHASE_TOKEN
    _schema = VERIFIED_ZDEX_AMM_PURCHASE_SCHEMA_V1
    _domain = "verified-zdex-amm-purchase-v1"


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

    if type(candidate) is not ZDEXPurchaseReceiptCandidateV1:
        raise TypeError("ZDEX purchase receipt candidate must be exact typed data")
    _require_release_and_occurrence(
        candidate.route_release,
        candidate.module_release,
        candidate.occurrence,
        lane_id=LaneIdV1.SPOT_LIQUIDITY,
        route_index=0,
    )
    journal = candidate.journal
    occurrence = candidate.occurrence
    bindings = (
        (journal.chain_id, occurrence.chain_id, "chain"),
        (journal.deployment_root, occurrence.deployment_root, "deployment"),
        (journal.profile_root, occurrence.profile_root, "profile"),
        (journal.route_release_id, candidate.route_release.route_release_id, "route"),
        (journal.command_occurrence_id, occurrence.occurrence_id, "occurrence"),
        (journal.spot_module_release_id, candidate.module_release.release_id, "module release"),
        (
            journal.issue_burn_policy_root,
            candidate.route_release.issue_burn_policy_root,
            "issue/burn policy",
        ),
        (journal.effect_plan_root, candidate.effects.effect_plan_root, "effect plan"),
    )
    for actual, expected, label in bindings:
        if actual != expected:
            raise ValueError(f"ZDEX purchase {label} mismatch")
    if candidate.effects != purchase_effects_v1(journal):
        raise ValueError("ZDEX purchase effect rows or conservation mismatch")
    journal_bytes, journal_digest, receipt_digest = _receipt_digests(
        journal,
        candidate.receipt,
    )
    if len(journal_bytes) > candidate.module_release.max_journal_bytes:
        raise ValueError("ZDEX purchase journal exceeds release byte ceiling")
    receipt_verifier.verify_succinct_receipt(
        candidate.receipt.receipt_bytes,
        expected_image_id=candidate.module_release.guest_image_id,
        expected_journal_bytes=journal_bytes,
    )
    return VerifiedZDEXAMMPurchaseV1(
        _VERIFIED_PURCHASE_TOKEN,
        _VerifiedZDEXLaneFieldsV1(
            candidate.route_release.route_release_id,
            candidate.module_release.release_id,
            occurrence.occurrence_id,
            occurrence.profile_root,
            journal.writer_epoch,
            journal.journal_root,
            journal_digest,
            candidate.effects.effect_plan_root,
            candidate.module_release.guest_image_id,
            receipt_digest,
            candidate.receipt.receipt_kind,
        ),
    )


def verify_zdex_burn_receipt_v1(
    candidate: ZDEXBurnReceiptCandidateV1,
    receipt_verifier: ZDEXLaneSuccinctReceiptVerifierV1,
) -> VerifiedZDEXBurnV1:
    """Authenticate exact burn output under its release-selected shadow image."""

    if type(candidate) is not ZDEXBurnReceiptCandidateV1:
        raise TypeError("ZDEX burn receipt candidate must be exact typed data")
    _require_release_and_occurrence(
        candidate.route_release,
        candidate.module_release,
        candidate.occurrence,
        lane_id=LaneIdV1.ZDEX_TOKENOMICS,
        route_index=1,
    )
    journal = candidate.journal
    occurrence = candidate.occurrence
    bindings = (
        (journal.chain_id, occurrence.chain_id, "chain"),
        (journal.deployment_root, occurrence.deployment_root, "deployment"),
        (journal.profile_root, occurrence.profile_root, "profile"),
        (journal.route_release_id, candidate.route_release.route_release_id, "route"),
        (journal.command_occurrence_id, occurrence.occurrence_id, "occurrence"),
        (
            journal.tokenomics_module_release_id,
            candidate.module_release.release_id,
            "module release",
        ),
        (
            journal.issue_burn_policy_root,
            candidate.route_release.issue_burn_policy_root,
            "issue/burn policy",
        ),
        (journal.effect_plan_root, candidate.effects.effect_plan_root, "effect plan"),
    )
    for actual, expected, label in bindings:
        if actual != expected:
            raise ValueError(f"ZDEX burn {label} mismatch")
    if candidate.effects != burn_effects_v1(journal):
        raise ValueError("ZDEX burn effect rows or conservation mismatch")
    journal_bytes, journal_digest, receipt_digest = _receipt_digests(
        journal,
        candidate.receipt,
    )
    if len(journal_bytes) > candidate.module_release.max_journal_bytes:
        raise ValueError("ZDEX burn journal exceeds release byte ceiling")
    receipt_verifier.verify_succinct_receipt(
        candidate.receipt.receipt_bytes,
        expected_image_id=candidate.module_release.guest_image_id,
        expected_journal_bytes=journal_bytes,
    )
    return VerifiedZDEXBurnV1(
        _VERIFIED_BURN_TOKEN,
        _VerifiedZDEXLaneFieldsV1(
            candidate.route_release.route_release_id,
            candidate.module_release.release_id,
            occurrence.occurrence_id,
            occurrence.profile_root,
            journal.writer_epoch,
            journal.journal_root,
            journal_digest,
            candidate.effects.effect_plan_root,
            candidate.module_release.guest_image_id,
            receipt_digest,
            candidate.receipt.receipt_kind,
        ),
    )


__all__ = [
    "VERIFIED_ZDEX_AMM_PURCHASE_SCHEMA_V1",
    "VERIFIED_ZDEX_BURN_SCHEMA_V1",
    "VerifiedZDEXAMMPurchaseV1",
    "VerifiedZDEXBurnV1",
    "ZDEXBurnReceiptCandidateV1",
    "ZDEXLaneReceiptEnvelopeV1",
    "ZDEXLaneSuccinctReceiptVerifierV1",
    "ZDEXPurchaseReceiptCandidateV1",
    "verify_zdex_amm_purchase_receipt_v1",
    "verify_zdex_burn_receipt_v1",
]
