"""Receipt preparation for the legacy ZDEX purchase V1/V2 and burn V1 leaves.

The pure core snapshots each candidate, runs every release, occurrence,
journal, effect, price-authority and receipt-shape check, and fixes the exact
module receipt request (receipt bytes, module image, canonical journal bytes)
plus the complete marker fields as one prepared subject.  It performs no
verifier call.  ``src.integration.zdex_purchase_burn_receipt_verification_v1``
executes a prepared subject on the caller-supplied verifier and mints the
existing markers from the executed copy only.

Governed preparers consume an already-owned profile and authority head plus
the checked verifier binding root as plain data.  The shared Bound-verifier
authority helper stays in ``zdex_purchase_burn_receipt_verification_v1`` as
explicit core debt; the shell sequences it before preparation.

Prepared data and the private factories carry no cryptographic or publication
authority.  Every marker remains a shadow/reference marker.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, replace
from typing import TypeVar

from .global_economic_authority_head_v1 import GlobalEconomicAuthorityHeadV1
from .global_economic_capability_profile_binding_v1 import (
    snapshot_economic_policy_registry_v1,
)
from .global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from .global_economic_proof_v1 import ReceiptKindV1
from .global_economic_refinement_snapshot_v1 import (
    _require_exact_dataclass_scalars_v1,
)
from .global_settlement_types_v1 import (
    ZERO_ROOT_V1,
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    LaneIdV1,
    _require_root,
)
from .zdex_buyback_price_authority_v1 import (
    ZDEXBuybackPriceAuthorityCandidateV1,
    verify_zdex_buyback_price_authority_v1,
)
from .zdex_buyback_price_safety_v1 import ZDEX_BUYBACK_PRICE_SAFETY_POLICY_KIND_V1
from .zdex_fee_allocation_types_v1 import FEE_BUYBACK_PRINCIPAL_V1
from .zdex_purchase_burn_effects_v1 import (
    burn_effects_v1,
    purchase_effects_v1,
    purchase_effects_v2,
)
from .zdex_purchase_burn_receipt_verification_v1 import (
    _GOVERNED_VERIFIED_PURCHASE_V2_TOKEN,
    _VERIFIED_BURN_TOKEN,
    _VERIFIED_PURCHASE_TOKEN,
    _VERIFIED_PURCHASE_V2_TOKEN,
    GovernedVerifiedZDEXAMMPurchaseV2,
    VerifiedZDEXAMMPurchaseV1,
    VerifiedZDEXAMMPurchaseV2,
    VerifiedZDEXBurnV1,
    ZDEXBurnReceiptCandidateV1,
    ZDEXPurchaseReceiptCandidateV1,
    ZDEXPurchaseReceiptCandidateV2,
    _GovernedVerifiedZDEXAMMPurchaseFieldsV2,
    _receipt_digests,
    _require_release_and_occurrence,
    _snapshot_burn_candidate_v1,
    _snapshot_purchase_candidate_v1,
    _snapshot_purchase_candidate_v2,
    _VerifiedZDEXLaneFieldsV1,
    _ZDEXBurnReceiptSnapshotV1,
    _ZDEXPurchaseReceiptSnapshotV1,
    _ZDEXPurchaseReceiptSnapshotV2,
)
from .zdex_purchase_burn_route_types_v1 import (
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    ZDEX_BUYBACK_EXECUTION_POLICY_KIND_V1,
    zdex_occurrence_burn_port_v1,
    zdex_pool_reserve_principal_v1,
)


@dataclass(frozen=True, slots=True)
class PreparedZDEXAMMPurchaseReceiptV1:
    """Complete pure execution subject for one V1 purchase leaf.

    Data only.  Holding this record is not evidence that any verifier ran; the
    shell executes it and mints the marker from its own detached snapshot.  The
    expected image is the marker's own ``expected_image_id`` (the module
    release image), so no duplicated request field can disagree with the
    minted marker.
    """

    verified_fields: _VerifiedZDEXLaneFieldsV1
    receipt_bytes: bytes
    expected_journal_bytes: bytes

    def __post_init__(self) -> None:
        _require_prepared_record_types_v1(self, name="prepared ZDEX purchase")

    @property
    def expected_image_id(self) -> str:
        return self.verified_fields.expected_image_id


@dataclass(frozen=True, slots=True)
class PreparedZDEXAMMPurchaseReceiptV2:
    """Complete pure execution subject for one V2 purchase leaf (price-bound)."""

    verified_fields: _VerifiedZDEXLaneFieldsV1
    receipt_bytes: bytes
    expected_journal_bytes: bytes

    def __post_init__(self) -> None:
        _require_prepared_record_types_v1(self, name="prepared ZDEX purchase V2")

    @property
    def expected_image_id(self) -> str:
        return self.verified_fields.expected_image_id


@dataclass(frozen=True, slots=True)
class PreparedZDEXBurnReceiptV1:
    """Complete pure execution subject for one V1 burn leaf."""

    verified_fields: _VerifiedZDEXLaneFieldsV1
    receipt_bytes: bytes
    expected_journal_bytes: bytes

    def __post_init__(self) -> None:
        _require_prepared_record_types_v1(self, name="prepared ZDEX burn")

    @property
    def expected_image_id(self) -> str:
        return self.verified_fields.expected_image_id


@dataclass(frozen=True, slots=True)
class PreparedGovernedZDEXAMMPurchaseReceiptV2:
    """Prepared V2 leaf plus the owned current-authority coordinates.

    The leaf keeps zero authority roots exactly as the old governed wrapper
    produced; the three roots here are fixed before any I/O from the owned
    head, the checked verifier binding and the owned policy registry.
    """

    leaf: PreparedZDEXAMMPurchaseReceiptV2
    authority_head_root: str
    verifier_binding_root: str
    policy_registry_root: str

    def __post_init__(self) -> None:
        if type(self.leaf) is not PreparedZDEXAMMPurchaseReceiptV2:
            raise TypeError("prepared governed ZDEX purchase V2 leaf must be exact typed data")
        for value, name in (
            (self.authority_head_root, "authority head"),
            (self.verifier_binding_root, "verifier binding"),
            (self.policy_registry_root, "policy registry"),
        ):
            if type(value) is not str:
                raise TypeError(
                    f"prepared governed ZDEX purchase V2 {name} root must be exact str"
                )
            _require_root(value, name=f"prepared governed ZDEX purchase V2 {name} root")

    @property
    def expected_image_id(self) -> str:
        return self.leaf.expected_image_id


_PreparedLeafT = TypeVar(
    "_PreparedLeafT",
    PreparedZDEXAMMPurchaseReceiptV1,
    PreparedZDEXAMMPurchaseReceiptV2,
    PreparedZDEXBurnReceiptV1,
)


@dataclass(frozen=True, slots=True)
class _ZDEXGovernedReceiptAuthorityV1:
    """Owned, checked authority coordinates consumed by governed preparation."""

    authority_epoch: int
    policy_registry_root: str
    authority_head_root: str
    verifier_binding_root: str


def _sha256_root_v1(value: bytes) -> str:
    return "0x" + hashlib.sha256(value).hexdigest()


def _require_prepared_record_types_v1(
    prepared: (
        PreparedZDEXAMMPurchaseReceiptV1
        | PreparedZDEXAMMPurchaseReceiptV2
        | PreparedZDEXBurnReceiptV1
    ),
    *,
    name: str,
) -> None:
    if type(prepared.verified_fields) is not _VerifiedZDEXLaneFieldsV1:
        raise TypeError(f"{name} fields must be exact typed data")
    if type(prepared.receipt_bytes) is not bytes:
        raise TypeError(f"{name} receipt bytes must be exact bytes")
    if type(prepared.expected_journal_bytes) is not bytes:
        raise TypeError(f"{name} journal bytes must be exact bytes")


def _require_prepared_digests_v1(prepared: _PreparedLeafT, *, name: str) -> None:
    """Bind the digest fields to the exact request bytes that will be executed."""

    fields = prepared.verified_fields
    if fields.receipt_digest != _sha256_root_v1(prepared.receipt_bytes):
        raise ValueError(f"{name} receipt digest mismatch")
    if fields.journal_digest != _sha256_root_v1(prepared.expected_journal_bytes):
        raise ValueError(f"{name} journal digest mismatch")


def _snapshot_prepared_leaf_receipt_v1(
    prepared: _PreparedLeafT,
    expected_type: type[_PreparedLeafT],
    *,
    name: str,
) -> _PreparedLeafT:
    """Return a validated detached copy of one prepared leaf subject.

    Exact record, scalar, enum and byte types plus digest-to-bytes binding are
    rechecked.  No further release restriction is added: each preparation
    entry point's own upstream validators fix the acceptance domain, exactly
    as before the extraction.
    """

    if type(prepared) is not expected_type:
        raise TypeError(f"{name} receipt must be exact typed data")
    fields = prepared.verified_fields
    if type(fields) is not _VerifiedZDEXLaneFieldsV1:
        raise TypeError(f"{name} fields must be exact typed data")
    _require_exact_dataclass_scalars_v1(fields, name=name)
    if type(fields.receipt_kind) is not ReceiptKindV1:
        raise TypeError(f"{name} receipt kind is not closed")
    if type(prepared.receipt_bytes) is not bytes:
        raise TypeError(f"{name} receipt bytes must be exact bytes")
    if type(prepared.expected_journal_bytes) is not bytes:
        raise TypeError(f"{name} journal bytes must be exact bytes")
    _require_prepared_digests_v1(prepared, name=name)
    return expected_type(
        replace(fields),
        prepared.receipt_bytes,
        prepared.expected_journal_bytes,
    )


def snapshot_prepared_zdex_amm_purchase_receipt_v1(
    prepared: PreparedZDEXAMMPurchaseReceiptV1,
) -> PreparedZDEXAMMPurchaseReceiptV1:
    return _snapshot_prepared_leaf_receipt_v1(
        prepared,
        PreparedZDEXAMMPurchaseReceiptV1,
        name="prepared ZDEX purchase",
    )


def snapshot_prepared_zdex_amm_purchase_receipt_v2(
    prepared: PreparedZDEXAMMPurchaseReceiptV2,
) -> PreparedZDEXAMMPurchaseReceiptV2:
    return _snapshot_prepared_leaf_receipt_v1(
        prepared,
        PreparedZDEXAMMPurchaseReceiptV2,
        name="prepared ZDEX purchase V2",
    )


def snapshot_prepared_zdex_burn_receipt_v1(
    prepared: PreparedZDEXBurnReceiptV1,
) -> PreparedZDEXBurnReceiptV1:
    return _snapshot_prepared_leaf_receipt_v1(
        prepared,
        PreparedZDEXBurnReceiptV1,
        name="prepared ZDEX burn",
    )


def snapshot_prepared_governed_zdex_amm_purchase_receipt_v2(
    prepared: PreparedGovernedZDEXAMMPurchaseReceiptV2,
) -> PreparedGovernedZDEXAMMPurchaseReceiptV2:
    """Return a validated detached copy of one governed V2 prepared subject."""

    if type(prepared) is not PreparedGovernedZDEXAMMPurchaseReceiptV2:
        raise TypeError("prepared governed ZDEX purchase V2 receipt must be exact typed data")
    return PreparedGovernedZDEXAMMPurchaseReceiptV2(
        snapshot_prepared_zdex_amm_purchase_receipt_v2(prepared.leaf),
        prepared.authority_head_root,
        prepared.verifier_binding_root,
        prepared.policy_registry_root,
    )


def _build_verified_zdex_amm_purchase_v1(
    prepared: PreparedZDEXAMMPurchaseReceiptV1,
) -> VerifiedZDEXAMMPurchaseV1:
    """Mint the existing V1 purchase marker from one validated prepared subject.

    Deterministic data construction only.  Post-callback sequencing belongs to
    the shell, which calls this with the detached snapshot it executed.  The
    marker carries no authority and this factory is not a verifier.
    """

    owned = snapshot_prepared_zdex_amm_purchase_receipt_v1(prepared)
    return VerifiedZDEXAMMPurchaseV1(_VERIFIED_PURCHASE_TOKEN, owned.verified_fields)


def _build_verified_zdex_amm_purchase_v2(
    prepared: PreparedZDEXAMMPurchaseReceiptV2,
) -> VerifiedZDEXAMMPurchaseV2:
    """Mint the existing V2 purchase marker from one validated prepared subject."""

    owned = snapshot_prepared_zdex_amm_purchase_receipt_v2(prepared)
    return VerifiedZDEXAMMPurchaseV2(_VERIFIED_PURCHASE_V2_TOKEN, owned.verified_fields)


def _build_verified_zdex_burn_v1(
    prepared: PreparedZDEXBurnReceiptV1,
) -> VerifiedZDEXBurnV1:
    """Mint the existing burn marker from one validated prepared subject."""

    owned = snapshot_prepared_zdex_burn_receipt_v1(prepared)
    return VerifiedZDEXBurnV1(_VERIFIED_BURN_TOKEN, owned.verified_fields)


def _build_governed_verified_zdex_amm_purchase_v2(
    prepared: PreparedGovernedZDEXAMMPurchaseReceiptV2,
) -> GovernedVerifiedZDEXAMMPurchaseV2:
    """Mint the existing governed V2 marker from one validated prepared subject."""

    owned = snapshot_prepared_governed_zdex_amm_purchase_receipt_v2(prepared)
    return GovernedVerifiedZDEXAMMPurchaseV2(
        _GOVERNED_VERIFIED_PURCHASE_V2_TOKEN,
        _GovernedVerifiedZDEXAMMPurchaseFieldsV2(
            verified_leaf=_build_verified_zdex_amm_purchase_v2(owned.leaf),
            authority_head_root=owned.authority_head_root,
            verifier_binding_root=owned.verifier_binding_root,
            policy_registry_root=owned.policy_registry_root,
        ),
    )


def snapshot_zdex_purchase_receipt_candidate_v1(
    candidate: ZDEXPurchaseReceiptCandidateV1,
) -> ZDEXPurchaseReceiptCandidateV1:
    """Own and revalidate a V1 purchase candidate as the same candidate type."""

    owned = _snapshot_purchase_candidate_v1(candidate)
    return ZDEXPurchaseReceiptCandidateV1(
        owned.route_release,
        owned.module_release,
        owned.occurrence,
        owned.journal,
        owned.effects,
        owned.receipt,
    )


def snapshot_zdex_purchase_receipt_candidate_v2(
    candidate: ZDEXPurchaseReceiptCandidateV2,
) -> ZDEXPurchaseReceiptCandidateV2:
    """Own and revalidate a V2 purchase candidate as the same candidate type."""

    owned = _snapshot_purchase_candidate_v2(candidate)
    return ZDEXPurchaseReceiptCandidateV2(
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
    )


def snapshot_zdex_burn_receipt_candidate_v1(
    candidate: ZDEXBurnReceiptCandidateV1,
) -> ZDEXBurnReceiptCandidateV1:
    """Own and revalidate a burn candidate as the same candidate type."""

    owned = _snapshot_burn_candidate_v1(candidate)
    return ZDEXBurnReceiptCandidateV1(
        owned.route_release,
        owned.module_release,
        owned.occurrence,
        owned.journal,
        owned.effects,
        owned.receipt,
    )


def snapshot_governed_receipt_authority_head_v1(
    authority_head: GlobalEconomicAuthorityHeadV1,
) -> GlobalEconomicAuthorityHeadV1:
    """Own the exact typed authority head; the copy reruns the head's own checks."""

    if type(authority_head) is not GlobalEconomicAuthorityHeadV1:
        raise TypeError("ZDEX governed receipt authority head must be exact typed data")
    return replace(authority_head)


def _snapshot_governed_authority_v1(
    *,
    profile: EconomicProfileSnapshotV1,
    authority_head: GlobalEconomicAuthorityHeadV1,
    verifier_binding_root: str,
) -> _ZDEXGovernedReceiptAuthorityV1:
    """Own the governed coordinates that the shell checked before preparation.

    The verifier binding root is the value the shell captured from the Bound
    verifier before any I/O; it must equal the owned head's own binding root,
    which the retained authority helper already compared against the verifier.
    """

    owned_profile = snapshot_economic_profile_v1(profile)
    owned_head = snapshot_governed_receipt_authority_head_v1(authority_head)
    if type(verifier_binding_root) is not str:
        raise TypeError("ZDEX governed receipt verifier binding root must be exact str")
    _require_root(verifier_binding_root, name="ZDEX governed receipt verifier binding root")
    if verifier_binding_root != owned_head.verifier_binding_root:
        raise ValueError("ZDEX governed receipt verifier binding root is outside the head")
    return _ZDEXGovernedReceiptAuthorityV1(
        owned_profile.authority_epoch,
        owned_profile.policy_registry_root,
        owned_head.authority_root,
        verifier_binding_root,
    )


def _require_purchase_bindings_v1(owned: _ZDEXPurchaseReceiptSnapshotV1) -> None:
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


def _require_purchase_bindings_v2(owned: _ZDEXPurchaseReceiptSnapshotV2) -> None:
    journal = owned.journal
    occurrence = owned.occurrence
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
            journal.buyback_execution_policy_root != owned.execution_policy.policy_root,
            journal.price_safety_policy_root != owned.price_policy.policy_root,
            journal.oracle_occurrence_root != owned.price_occurrence.occurrence_root,
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


def _require_purchase_price_authority_v2(owned: _ZDEXPurchaseReceiptSnapshotV2) -> str:
    """Run the pre-receipt price authority check and return its authority root."""

    journal = owned.journal
    price_authority = verify_zdex_buyback_price_authority_v1(
        ZDEXBuybackPriceAuthorityCandidateV1(
            pre_state=owned.pre_state,
            route=owned.route_release,
            occurrence=owned.occurrence,
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
    return price_authority.authority_root


def _require_burn_bindings_v1(owned: _ZDEXBurnReceiptSnapshotV1) -> None:
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


def prepare_zdex_amm_purchase_receipt_v1(
    candidate: ZDEXPurchaseReceiptCandidateV1,
) -> PreparedZDEXAMMPurchaseReceiptV1:
    """Fix one exact AMM output's module receipt request with no verifier call.

    Reject precedence is unchanged from the former effectful entry point:
    candidate snapshot, route shape, release and occurrence, journal bindings,
    effect recomputation, succinct receipt kind, nonempty receipt bytes, then
    the module release journal byte ceiling.  Authority roots stay zero.
    """

    owned = _snapshot_purchase_candidate_v1(candidate)
    _require_release_and_occurrence(
        owned.route_release,
        owned.module_release,
        owned.occurrence,
        lane_id=LaneIdV1.SPOT_LIQUIDITY,
        route_index=0,
    )
    _require_purchase_bindings_v1(owned)
    journal = owned.journal
    journal_bytes, journal_digest, receipt_digest = _receipt_digests(journal, owned.receipt)
    if len(journal_bytes) > owned.module_release.max_journal_bytes:
        raise ValueError("ZDEX purchase journal exceeds release byte ceiling")
    return PreparedZDEXAMMPurchaseReceiptV1(
        _VerifiedZDEXLaneFieldsV1(
            owned.route_release.route_release_id,
            owned.module_release.release_id,
            owned.occurrence.occurrence_id,
            owned.occurrence.profile_root,
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
        owned.receipt.receipt_bytes,
        journal_bytes,
    )


def prepare_zdex_amm_purchase_receipt_v2(
    candidate: ZDEXPurchaseReceiptCandidateV2,
) -> PreparedZDEXAMMPurchaseReceiptV2:
    """Fix one price-bound purchase's module receipt request with no verifier call.

    Reject precedence is unchanged: candidate snapshot, route shape, release
    and occurrence, journal/effects mismatch, price authority (a real
    pre-receipt check), succinct receipt kind, nonempty receipt bytes, then
    the module release journal byte ceiling.  Authority roots stay zero.
    """

    owned = _snapshot_purchase_candidate_v2(candidate)
    _require_release_and_occurrence(
        owned.route_release,
        owned.module_release,
        owned.occurrence,
        lane_id=LaneIdV1.SPOT_LIQUIDITY,
        route_index=0,
    )
    _require_purchase_bindings_v2(owned)
    price_authority_root = _require_purchase_price_authority_v2(owned)
    journal = owned.journal
    journal_bytes, journal_digest, receipt_digest = _receipt_digests(journal, owned.receipt)
    if len(journal_bytes) > owned.module_release.max_journal_bytes:
        raise ValueError("ZDEX purchase V2 journal exceeds release byte ceiling")
    return PreparedZDEXAMMPurchaseReceiptV2(
        _VerifiedZDEXLaneFieldsV1(
            route_release_id=owned.route_release.route_release_id,
            module_release_id=owned.module_release.release_id,
            command_occurrence_id=owned.occurrence.occurrence_id,
            profile_root=owned.occurrence.profile_root,
            writer_epoch=journal.writer_epoch,
            journal_root=journal.journal_root,
            journal_digest=journal_digest,
            effect_plan_root=owned.effects.effect_plan_root,
            expected_image_id=owned.module_release.guest_image_id,
            receipt_digest=receipt_digest,
            receipt_kind=owned.receipt.receipt_kind,
            authority_head_root=ZERO_ROOT_V1,
            verifier_binding_root=ZERO_ROOT_V1,
            price_authority_root=price_authority_root,
            price_safety_policy_root=owned.price_policy.policy_root,
        ),
        owned.receipt.receipt_bytes,
        journal_bytes,
    )


def prepare_zdex_burn_receipt_v1(
    candidate: ZDEXBurnReceiptCandidateV1,
) -> PreparedZDEXBurnReceiptV1:
    """Fix one exact burn output's module receipt request with no verifier call.

    Reject precedence is unchanged from the former effectful entry point:
    candidate snapshot, route shape, release and occurrence, journal bindings,
    effect recomputation, succinct receipt kind, nonempty receipt bytes, then
    the module release journal byte ceiling.  Authority roots stay zero.
    """

    owned = _snapshot_burn_candidate_v1(candidate)
    _require_release_and_occurrence(
        owned.route_release,
        owned.module_release,
        owned.occurrence,
        lane_id=LaneIdV1.ZDEX_TOKENOMICS,
        route_index=1,
    )
    _require_burn_bindings_v1(owned)
    journal = owned.journal
    journal_bytes, journal_digest, receipt_digest = _receipt_digests(journal, owned.receipt)
    if len(journal_bytes) > owned.module_release.max_journal_bytes:
        raise ValueError("ZDEX burn journal exceeds release byte ceiling")
    return PreparedZDEXBurnReceiptV1(
        _VerifiedZDEXLaneFieldsV1(
            owned.route_release.route_release_id,
            owned.module_release.release_id,
            owned.occurrence.occurrence_id,
            owned.occurrence.profile_root,
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
        owned.receipt.receipt_bytes,
        journal_bytes,
    )


def prepare_governed_zdex_amm_purchase_receipt_shadow_v1(
    candidate: ZDEXPurchaseReceiptCandidateV1,
    *,
    profile: EconomicProfileSnapshotV1,
    authority_head: GlobalEconomicAuthorityHeadV1,
    verifier_binding_root: str,
) -> PreparedZDEXAMMPurchaseReceiptV1:
    """Prepare a governed V1 purchase leaf from owned authority coordinates.

    The shell has already run the retained current-authority helper on the
    owned head and verifier.  This preparer owns its inputs again, applies the
    writer-epoch check, runs the generic V1 preparation, then fixes the head
    and verifier binding roots into the marker fields before any I/O.
    """

    owned = snapshot_zdex_purchase_receipt_candidate_v1(candidate)
    authority = _snapshot_governed_authority_v1(
        profile=profile,
        authority_head=authority_head,
        verifier_binding_root=verifier_binding_root,
    )
    if owned.journal.writer_epoch != authority.authority_epoch:
        raise ValueError("ZDEX purchase receipt writer epoch is outside the profile")
    prepared = prepare_zdex_amm_purchase_receipt_v1(owned)
    return PreparedZDEXAMMPurchaseReceiptV1(
        replace(
            prepared.verified_fields,
            authority_head_root=authority.authority_head_root,
            verifier_binding_root=authority.verifier_binding_root,
        ),
        prepared.receipt_bytes,
        prepared.expected_journal_bytes,
    )


def prepare_governed_zdex_amm_purchase_receipt_shadow_v2(
    candidate: ZDEXPurchaseReceiptCandidateV2,
    *,
    profile: EconomicProfileSnapshotV1,
    policy_registry: EconomicPolicyRegistryV1,
    authority_head: GlobalEconomicAuthorityHeadV1,
    verifier_binding_root: str,
) -> PreparedGovernedZDEXAMMPurchaseReceiptV2:
    """Prepare a governed V2 purchase leaf from owned authority coordinates.

    Reject precedence after the shell's authority helper is unchanged: policy
    registry root, execution binding presence, price binding presence,
    execution policy root, price policy root, writer epoch, then the generic
    V2 preparation.  The V2 leaf keeps zero authority roots; the governed
    record carries the head, verifier binding and registry roots.
    """

    owned = snapshot_zdex_purchase_receipt_candidate_v2(candidate)
    authority = _snapshot_governed_authority_v1(
        profile=profile,
        authority_head=authority_head,
        verifier_binding_root=verifier_binding_root,
    )
    owned_policy_registry = snapshot_economic_policy_registry_v1(policy_registry)
    if owned_policy_registry.registry_root != authority.policy_registry_root:
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
    if owned.journal.writer_epoch != authority.authority_epoch:
        raise ValueError("ZDEX purchase V2 receipt writer epoch is outside the profile")
    return PreparedGovernedZDEXAMMPurchaseReceiptV2(
        prepare_zdex_amm_purchase_receipt_v2(owned),
        authority.authority_head_root,
        authority.verifier_binding_root,
        owned_policy_registry.registry_root,
    )


def prepare_governed_zdex_burn_receipt_shadow_v1(
    candidate: ZDEXBurnReceiptCandidateV1,
    *,
    profile: EconomicProfileSnapshotV1,
    authority_head: GlobalEconomicAuthorityHeadV1,
    verifier_binding_root: str,
) -> PreparedZDEXBurnReceiptV1:
    """Prepare a governed burn leaf from owned authority coordinates."""

    owned = snapshot_zdex_burn_receipt_candidate_v1(candidate)
    authority = _snapshot_governed_authority_v1(
        profile=profile,
        authority_head=authority_head,
        verifier_binding_root=verifier_binding_root,
    )
    if owned.journal.writer_epoch != authority.authority_epoch:
        raise ValueError("ZDEX burn receipt writer epoch is outside the profile")
    prepared = prepare_zdex_burn_receipt_v1(owned)
    return PreparedZDEXBurnReceiptV1(
        replace(
            prepared.verified_fields,
            authority_head_root=authority.authority_head_root,
            verifier_binding_root=authority.verifier_binding_root,
        ),
        prepared.receipt_bytes,
        prepared.expected_journal_bytes,
    )


__all__ = [
    "PreparedGovernedZDEXAMMPurchaseReceiptV2",
    "PreparedZDEXAMMPurchaseReceiptV1",
    "PreparedZDEXAMMPurchaseReceiptV2",
    "PreparedZDEXBurnReceiptV1",
    "prepare_governed_zdex_amm_purchase_receipt_shadow_v1",
    "prepare_governed_zdex_amm_purchase_receipt_shadow_v2",
    "prepare_governed_zdex_burn_receipt_shadow_v1",
    "prepare_zdex_amm_purchase_receipt_v1",
    "prepare_zdex_amm_purchase_receipt_v2",
    "prepare_zdex_burn_receipt_v1",
    "snapshot_governed_receipt_authority_head_v1",
    "snapshot_prepared_governed_zdex_amm_purchase_receipt_v2",
    "snapshot_prepared_zdex_amm_purchase_receipt_v1",
    "snapshot_prepared_zdex_amm_purchase_receipt_v2",
    "snapshot_prepared_zdex_burn_receipt_v1",
    "snapshot_zdex_burn_receipt_candidate_v1",
    "snapshot_zdex_purchase_receipt_candidate_v1",
    "snapshot_zdex_purchase_receipt_candidate_v2",
]
