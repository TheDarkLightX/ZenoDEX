"""Controlled derivation of one authoritative commit bundle from one decision.

A decoded ``CommitBundleClaimV1`` is replay/verifier data.  Only this module may
mint the authoritative ``CommitBundleV1`` wrapper from one controlled
``DecisionV1``.  All stored hashes, bytes, outbox identities, and idempotency
keys are derived inside the controlled builder.  No public constructor or
parameter accepts them.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from typing import TypeAlias, cast, final

from ..state.canonical import (
    canonical_json_bytes,
    domain_sep_bytes,
    hex_to_bytes_fixed,
    sha256_hex,
)
from ..state.fcis_committed_state_values import FCISCommittedStateV1
from ..state.owned_json import (
    OwnedJsonObjectV1,
    project_owned_json,
)
from ..state.snapshot_combinators import AdmitOk
from .fcis_authority_admission import (
    CanonicalAuthorityClaimBytesV1,
    admit_fcis_authority_claim_v1,
    encode_fcis_authority_claim_v1,
)
from .fcis_commit_bundle_values import (
    FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1,
    CommitBundleClaimV1,
    CommitBundleSourceV1,
)
from .fcis_decision_derivation import (
    AcceptV1,
    CommittedFailureV1,
    DecisionV1,
    RejectV1,
    _bundle_derivation_reject_v1,
    _claim_root_v1,
)
from .fcis_decision_values import (
    FCIS_ACCEPTANCE_RECEIPT_SCHEMA_ID_V1,
    FCIS_COMMITTED_FAILURE_RECEIPT_SCHEMA_ID_V1,
    AcceptanceReceiptClaimV1,
    AcceptClaimV1,
    CommittedFailureClaimV1,
    CommittedFailureReceiptClaimV1,
)
from .fcis_outbox_values import (
    FCIS_OUTBOX_PLAN_SCHEMA_ID_V1,
    OutboxEffectKindV1,
    OutboxPlanSourceV1,
    OutboxPlanV1,
    OutboxRecordSourceV1,
)
from .fcis_transition_values import CommitPlanV1

_COMMIT_BUNDLE_CONSTRUCTION_TOKEN_V1 = object()

_EFFECT_IDENTITY_DOMAIN_SEP_V1 = "zenodex/fcis/outbox-effect-identity"
_IDEMPOTENCY_DOMAIN_SEP_V1 = "zenodex/fcis/outbox-idempotency"
_CANONICAL_EVENT_KIND_V1 = OutboxEffectKindV1.CANONICAL_EVENT


@final
@dataclass(frozen=True, slots=True)
class CommitBundleV1:
    """One authoritative commit bundle retaining one committable decision.

    Successor state, plan, receipt, replay, and effects are reached through
    ``decision`` rather than copied into independently swappable fields.  The
    cached canonical bytes and bundle root are derived inside the controlled
    builder and recomputed by the reference commit port before publication.
    """

    decision: AcceptV1 | CommittedFailureV1
    outbox_plan: OutboxPlanV1
    _canonical_bundle_bytes: bytes
    _bundle_root: str
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _COMMIT_BUNDLE_CONSTRUCTION_TOKEN_V1:
            raise TypeError("CommitBundleV1 requires controlled derivation")
        if type(self.decision) not in (AcceptV1, CommittedFailureV1):
            raise TypeError("bundle decision must be an exact committable decision")
        if type(self.outbox_plan) is not OutboxPlanV1:
            raise TypeError("bundle outbox_plan must be exact")
        if type(self._canonical_bundle_bytes) is not bytes:
            raise TypeError("bundle canonical bytes must be exact bytes")
        if type(self._bundle_root) is not str or not self._bundle_root.startswith("0x"):
            raise TypeError("bundle root must be a canonical digest")
        hex_to_bytes_fixed(self._bundle_root, nbytes=32, name="bundle_root")

    @property
    def next_state(self) -> FCISCommittedStateV1:
        return self.decision.next_state

    @property
    def commit_plan(self) -> CommitPlanV1:
        return self.decision.commit_plan

    @property
    def receipt(self) -> AcceptanceReceiptClaimV1 | CommittedFailureReceiptClaimV1:
        return self.decision.receipt

    @property
    def receipt_root(self) -> str:
        schema_id = (
            FCIS_ACCEPTANCE_RECEIPT_SCHEMA_ID_V1
            if type(self.decision) is AcceptV1
            else FCIS_COMMITTED_FAILURE_RECEIPT_SCHEMA_ID_V1
        )
        _, root = _claim_root_v1(schema_id, self.decision.receipt)
        return root

    @property
    def expected_pre_root(self) -> str:
        return self.decision.receipt.binding.pre_state_root

    @property
    def bundle_root(self) -> str:
        return self._bundle_root

    @property
    def canonical_bundle_bytes(self) -> bytes:
        return self._canonical_bundle_bytes


CommitBundleBuildResultV1: TypeAlias = CommitBundleV1 | RejectV1


def _raw32(digest_hex: str) -> bytes:
    """Convert a canonical lowercase 0x 32-byte digest to raw bytes."""

    return hex_to_bytes_fixed(digest_hex, nbytes=32, name="digest")


def _u32_be(value: int) -> bytes:
    """Encode one nonnegative int as a 4-byte big-endian unsigned integer."""

    if type(value) is not int or not 0 <= value < (1 << 32):
        raise ValueError("u32_be requires an exact bounded nonnegative int")
    return value.to_bytes(4, byteorder="big")


def _u64_be(value: int) -> bytes:
    """Encode one nonnegative int as an 8-byte big-endian unsigned integer."""

    if type(value) is not int or not 0 <= value < (1 << 64):
        raise ValueError("u64_be requires an exact bounded nonnegative int")
    return value.to_bytes(8, byteorder="big")


def _effect_identity_preimage_v1(
    receipt_root: str,
    index: int,
    kind_utf8: bytes,
    payload_bytes: bytes,
) -> bytes:
    """Construct the exact effect-identity preimage per the frozen formula.

    .. code-block:: text

        effect_identity_preimage_v1 =
          domain_sep("zenodex/fcis/outbox-effect-identity", 1)
          || raw32(receipt_root)
          || u32_be(i)
          || u32_be(len(kind_utf8)) || kind_utf8
          || u64_be(len(p)) || p
    """

    return (
        domain_sep_bytes(_EFFECT_IDENTITY_DOMAIN_SEP_V1, version=1)
        + _raw32(receipt_root)
        + _u32_be(index)
        + _u32_be(len(kind_utf8))
        + kind_utf8
        + _u64_be(len(payload_bytes))
        + payload_bytes
    )


def _idempotency_preimage_v1(
    receipt_root: str,
    index: int,
    effect_identity: str,
) -> bytes:
    """Construct the exact idempotency-key preimage per the frozen formula.

    .. code-block:: text

        idempotency_preimage_v1 =
          domain_sep("zenodex/fcis/outbox-idempotency", 1)
          || raw32(receipt_root)
          || u32_be(i)
          || raw32(effect_identity)
    """

    return (
        domain_sep_bytes(_IDEMPOTENCY_DOMAIN_SEP_V1, version=1)
        + _raw32(receipt_root)
        + _u32_be(index)
        + _raw32(effect_identity)
    )


def _canonical_event_payload_bytes(event: OwnedJsonObjectV1) -> bytes:
    """Encode one already-owned event payload using the repository JSON codec."""

    return canonical_json_bytes(project_owned_json(event))


def _derive_outbox_record_sources_v1(
    events: tuple[OwnedJsonObjectV1, ...],
    receipt_root: str,
) -> tuple[OutboxRecordSourceV1, ...]:
    """Derive outbox record sources from exact retained settlement events."""

    kind_utf8 = _CANONICAL_EVENT_KIND_V1.value.encode("utf-8")
    sources: list[OutboxRecordSourceV1] = []
    for index, event in enumerate(events):
        payload_bytes = _canonical_event_payload_bytes(event)
        identity_preimage = _effect_identity_preimage_v1(
            receipt_root,
            index,
            kind_utf8,
            payload_bytes,
        )
        effect_identity = sha256_hex(identity_preimage)
        idempotency_preimage = _idempotency_preimage_v1(
            receipt_root,
            index,
            effect_identity,
        )
        idempotency_key = sha256_hex(idempotency_preimage)
        sources.append(
            OutboxRecordSourceV1(
                effect_index=index,
                effect_kind=_CANONICAL_EVENT_KIND_V1,
                effect_identity=effect_identity,
                payload=event,
                idempotency_key=idempotency_key,
            )
        )
    return tuple(sources)


def _derive_outbox_plan_v1(
    events: tuple[OwnedJsonObjectV1, ...] | None,
    receipt_root: str,
) -> OutboxPlanV1:
    """Admit one same-decision outbox plan through the closed grammar."""

    event_tuple = () if events is None else events
    sources = _derive_outbox_record_sources_v1(event_tuple, receipt_root)
    plan_source = OutboxPlanSourceV1(records=sources)
    admitted = admit_fcis_authority_claim_v1(FCIS_OUTBOX_PLAN_SCHEMA_ID_V1, plan_source)
    if type(admitted) is not AdmitOk or type(admitted.value) is not OutboxPlanV1:
        raise ValueError("controlled outbox plan admission failed")
    return cast(OutboxPlanV1, admitted.value)


def _project_accept_claim_v1(decision: AcceptV1) -> AcceptClaimV1:
    """Project one controlled acceptance into its exact decoded claim form."""

    return AcceptClaimV1(
        decision.next_state,
        decision.commit_plan,
        decision.receipt,
    )


def _project_committed_failure_claim_v1(
    decision: CommittedFailureV1,
) -> CommittedFailureClaimV1:
    """Project one controlled committed-failure into its exact decoded claim form."""

    return CommittedFailureClaimV1(
        decision.next_state,
        decision.commit_plan,
        decision.receipt,
    )


def _derive_bundle_claim_v1(
    decision: AcceptV1 | CommittedFailureV1,
    outbox_plan: OutboxPlanV1,
) -> CommitBundleClaimV1:
    """Build and admit one bundle source through the closed authority grammar."""

    if type(decision) is AcceptV1:
        projected: AcceptClaimV1 | CommittedFailureClaimV1 = _project_accept_claim_v1(decision)
    elif type(decision) is CommittedFailureV1:
        projected = _project_committed_failure_claim_v1(decision)
    else:
        raise TypeError("bundle derivation requires an exact committable decision")
    receipt_root = (
        _receipt_root_for_decision_v1(decision)
        if type(decision) is AcceptV1
        else _committed_failure_receipt_root_v1(decision)
    )
    expected_pre_root = decision.receipt.binding.pre_state_root
    source = CommitBundleSourceV1(
        expected_pre_root=expected_pre_root,
        decision=projected,
        receipt_root=receipt_root,
        outbox_plan=outbox_plan,
    )
    admitted = admit_fcis_authority_claim_v1(FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1, source)
    if type(admitted) is not AdmitOk or type(admitted.value) is not CommitBundleClaimV1:
        raise ValueError("controlled bundle claim admission failed")
    claim = cast(CommitBundleClaimV1, admitted.value)
    if claim.decision != projected:
        raise ValueError("admitted bundle decision must equal the controlled projection")
    return claim


def _receipt_root_for_decision_v1(decision: AcceptV1) -> str:
    _, root = _claim_root_v1(FCIS_ACCEPTANCE_RECEIPT_SCHEMA_ID_V1, decision.receipt)
    return root


def _committed_failure_receipt_root_v1(decision: CommittedFailureV1) -> str:
    _, root = _claim_root_v1(
        FCIS_COMMITTED_FAILURE_RECEIPT_SCHEMA_ID_V1,
        decision.receipt,
    )
    return root


def _derive_bundle_root_v1(claim: object) -> tuple[bytes, str]:
    """Encode and hash one admitted bundle claim to derive canonical bytes and root."""

    if type(claim) is not CommitBundleClaimV1:
        raise TypeError("bundle root derivation requires an exact admitted claim")
    exact_claim = cast(CommitBundleClaimV1, claim)
    encoded = encode_fcis_authority_claim_v1(FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1, exact_claim)
    if type(encoded) is not CanonicalAuthorityClaimBytesV1:
        raise ValueError("controlled bundle canonical encoding failed")
    canonical_bytes = cast(CanonicalAuthorityClaimBytesV1, encoded).payload
    preimage = domain_sep_bytes(FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1, version=1) + canonical_bytes
    return canonical_bytes, sha256_hex(preimage)


def _build_bundle_v1(
    decision: AcceptV1 | CommittedFailureV1,
) -> CommitBundleV1:
    """Derive one controlled commit bundle from one committable decision."""

    events = decision.commit_plan.effects.settlement.events
    receipt_root = (
        _receipt_root_for_decision_v1(decision)
        if type(decision) is AcceptV1
        else _committed_failure_receipt_root_v1(decision)
    )
    outbox_plan = _derive_outbox_plan_v1(events, receipt_root)
    claim = _derive_bundle_claim_v1(decision, outbox_plan)
    canonical_bytes, bundle_root = _derive_bundle_root_v1(claim)
    return CommitBundleV1(
        decision,
        outbox_plan,
        canonical_bytes,
        bundle_root,
        _COMMIT_BUNDLE_CONSTRUCTION_TOKEN_V1,
    )


def build_commit_bundle_v1(decision: DecisionV1) -> CommitBundleBuildResultV1:
    """Return one controlled bundle from one decision, or the unchanged reject."""

    if type(decision) is RejectV1:
        return decision
    if type(decision) in (AcceptV1, CommittedFailureV1):
        try:
            return _build_bundle_v1(decision)
        except (OverflowError, TypeError, ValueError):
            return _bundle_derivation_reject_v1(decision)
    raise TypeError("build_commit_bundle_v1 requires an exact DecisionV1")


def recompute_bundle_root_v1(bundle: CommitBundleV1) -> tuple[bytes, str]:
    """Recompute canonical bundle bytes and root from the retained decision.

    The reference commit port calls this before publication because Python's
    ``frozen=True`` can be bypassed with ``object.__setattr__``.
    """

    if type(bundle) is not CommitBundleV1:
        raise TypeError("bundle root recomputation requires an exact CommitBundleV1")
    claim = _derive_bundle_claim_v1(bundle.decision, bundle.outbox_plan)
    return _derive_bundle_root_v1(claim)


def recompute_outbox_plan_v1(bundle: CommitBundleV1) -> OutboxPlanV1:
    """Recompute the outbox plan from the retained decision lineage."""

    if type(bundle) is not CommitBundleV1:
        raise TypeError("outbox recomputation requires an exact CommitBundleV1")
    events = bundle.decision.commit_plan.effects.settlement.events
    receipt_root = bundle.receipt_root
    return _derive_outbox_plan_v1(events, receipt_root)


__all__ = (
    "CommitBundleBuildResultV1",
    "CommitBundleV1",
    "build_commit_bundle_v1",
    "recompute_bundle_root_v1",
    "recompute_outbox_plan_v1",
)
