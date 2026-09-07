"""Publisher-bound execution shell for structurally prepared economic epochs.

Core (``src.core.global_economic_proof_v1``) prepares one exact detached
subject and performs no verifier call.  This shell executes exactly that
subject's receipt, image and canonical journal on the selected verifier, then
mints the process-local opaque witness that publishers require.  Handles are
registered under one lock in a weak registry keyed by handle identity; each
authority record retains the complete pure checked data plus the exact
publisher token and verifier object identity, compared by ``is`` only.

``SuccinctReceiptVerifierV1`` is the generic verifier port for shell callers.
Its return value is ignored, as the former core path did; the measured
``BoundEconomicReceiptVerifierV1`` enforces its own exact success contract
internally.  This module grants no production writer, settlement, consensus
or finality authority, and its private token and registry assume an intact
interpreter and process.
"""

from __future__ import annotations

from dataclasses import dataclass
from threading import Lock
from typing import Protocol
from weakref import WeakKeyDictionary

from ..core.economic_effect_occurrence_v1 import EconomicEffectOccurrenceV1
from ..core.global_economic_proof_v1 import (
    EconomicEpochReceiptCandidateV1,
    GlobalEconomicEpochCertificateV1,
    PreparedEconomicEpochV1,
    _require_exact_recheck_states_v1,
    _require_prepared_economic_epoch_v1,
    _snapshot_prepared_economic_epoch_v1,
    prepare_economic_epoch_v1,
)
from ..core.global_economic_refinement_snapshot_v1 import (
    _snapshot_effect_plan_v1,
    _snapshot_epoch_certificate_v1,
)
from ..core.global_economic_state_effect_refinement_v1 import (
    GlobalEconomicStateEffectRefinementV1,
    _snapshot_global_economic_state_effect_refinement_v1,
)
from ..core.global_settlement_types_v1 import (
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateV1,
)


class SuccinctReceiptVerifierV1(Protocol):
    """Port implemented by the release-selected cryptographic verifier."""

    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None: ...


_VERIFIED_ECONOMIC_EPOCH_TOKEN = object()


@dataclass(frozen=True, slots=True)
class _VerifiedEconomicEpochAuthorityRecordV1:
    """Shell-owned immutable source for one process-local opaque handle.

    ``prepared`` is the complete pure checked data.  The two identity fields
    are compared by ``is`` only: a matching raw root, a caller Boolean, a
    protocol-shaped success object or caller-constructed data never replaces
    the retained publisher token or verifier object.
    """

    prepared: PreparedEconomicEpochV1
    publisher_binding_token: object | None
    publisher_verifier_identity: object | None


def _snapshot_verified_economic_epoch_authority_record_v1(
    authority: _VerifiedEconomicEpochAuthorityRecordV1,
) -> _VerifiedEconomicEpochAuthorityRecordV1:
    if type(authority) is not _VerifiedEconomicEpochAuthorityRecordV1:
        raise TypeError("verified epoch authority record type is not closed")
    return _VerifiedEconomicEpochAuthorityRecordV1(
        prepared=_snapshot_prepared_economic_epoch_v1(authority.prepared),
        publisher_binding_token=authority.publisher_binding_token,
        publisher_verifier_identity=authority.publisher_verifier_identity,
    )


class VerifiedEconomicEpochV1:
    """Opaque epoch witness constructible only through this shell's verifiers."""

    __slots__ = ("__weakref__",)

    def __init__(
        self,
        token: object,
        authority: _VerifiedEconomicEpochAuthorityRecordV1,
    ) -> None:
        if token is not _VERIFIED_ECONOMIC_EPOCH_TOKEN:
            raise TypeError("VerifiedEconomicEpochV1 is verifier-constructed")
        _register_verified_economic_epoch_authority_v1(
            self,
            _snapshot_verified_economic_epoch_authority_record_v1(authority),
        )

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("VerifiedEconomicEpochV1 is immutable")

    @property
    def certificate(self) -> GlobalEconomicEpochCertificateV1:
        return _snapshot_epoch_certificate_v1(
            _verified_economic_epoch_prepared_v1(self).certificate
        )

    @property
    def effect_plan(self) -> GlobalEconomicEffectPlanV1:
        return _snapshot_effect_plan_v1(
            _verified_economic_epoch_prepared_v1(self).effect_plan
        )

    @property
    def effect_occurrences(self) -> tuple[EconomicEffectOccurrenceV1, ...]:
        """Return verifier-owned route effects with injective occurrence IDs."""

        return _verified_economic_epoch_prepared_v1(self).effect_occurrences

    @property
    def ordered_route_binding_roots(self) -> tuple[str, ...]:
        return _verified_economic_epoch_prepared_v1(self).ordered_route_binding_roots

    @property
    def ordered_command_body_hashes(self) -> tuple[str, ...]:
        return _verified_economic_epoch_prepared_v1(self).ordered_command_body_hashes

    @property
    def receipt_digest(self) -> str:
        return _verified_economic_epoch_prepared_v1(self).receipt_digest

    @property
    def verified_certificate_root(self) -> str:
        return _verified_economic_epoch_prepared_v1(self).certificate_root

    @property
    def verified_effect_plan_root(self) -> str:
        return _verified_economic_epoch_prepared_v1(self).effect_plan_root

    @property
    def verified_state_effect_refinement_root(self) -> str:
        return _verified_economic_epoch_prepared_v1(self).state_effect_refinement_root

    @property
    def route_state_projection_roots(self) -> tuple[str, ...]:
        return _verified_economic_epoch_prepared_v1(self).route_state_projection_roots

    @property
    def route_state_effect_refinement_roots(self) -> tuple[str, ...]:
        return _verified_economic_epoch_prepared_v1(
            self
        ).route_state_effect_refinement_roots

    @property
    def state_effect_refinement(self) -> GlobalEconomicStateEffectRefinementV1:
        return _snapshot_global_economic_state_effect_refinement_v1(
            _verified_economic_epoch_prepared_v1(self).state_effect_refinement
        )

    def recheck_state_effect_refinement(
        self,
        *,
        pre_state: GlobalEconomicStateV1,
        post_state: GlobalEconomicStateV1,
    ) -> GlobalEconomicStateEffectRefinementV1:
        """Recompute the full refinement from verifier-owned disclosures."""

        _require_exact_recheck_states_v1(pre_state=pre_state, post_state=post_state)
        return _verified_economic_epoch_prepared_v1(self).recheck_state_effect_refinement(
            pre_state=pre_state,
            post_state=post_state,
        )

    def recheck_route_state_projections(
        self,
        *,
        pre_state: GlobalEconomicStateV1,
        post_state: GlobalEconomicStateV1,
    ) -> tuple[str, ...]:
        """Recompute every route/full-state projection from owned disclosures."""

        projection_roots, _ = self.recheck_route_state_evidence(
            pre_state=pre_state,
            post_state=post_state,
        )
        return projection_roots

    def recheck_route_state_evidence(
        self,
        *,
        pre_state: GlobalEconomicStateV1,
        post_state: GlobalEconomicStateV1,
    ) -> tuple[tuple[str, ...], tuple[str, ...]]:
        """Recompute per-route projection and exact state/effect refinements."""

        return _verified_economic_epoch_prepared_v1(self).recheck_route_state_evidence(
            pre_state=pre_state,
            post_state=post_state,
        )

    @property
    def commit_id(self) -> str:
        return _verified_economic_epoch_prepared_v1(self).commit_id


_VERIFIED_ECONOMIC_EPOCH_AUTHORITY_LOCK = Lock()
_VERIFIED_ECONOMIC_EPOCH_AUTHORITIES: WeakKeyDictionary[
    VerifiedEconomicEpochV1,
    _VerifiedEconomicEpochAuthorityRecordV1,
] = WeakKeyDictionary()


def _register_verified_economic_epoch_authority_v1(
    witness: VerifiedEconomicEpochV1,
    authority: _VerifiedEconomicEpochAuthorityRecordV1,
) -> None:
    """Bind one exact handle identity to its shell-owned immutable record."""

    with _VERIFIED_ECONOMIC_EPOCH_AUTHORITY_LOCK:
        if witness in _VERIFIED_ECONOMIC_EPOCH_AUTHORITIES:
            raise RuntimeError("verified economic epoch handle is already registered")
        _VERIFIED_ECONOMIC_EPOCH_AUTHORITIES[witness] = authority


def _verified_economic_epoch_authority_v1(
    witness: VerifiedEconomicEpochV1,
) -> _VerifiedEconomicEpochAuthorityRecordV1:
    if type(witness) is not VerifiedEconomicEpochV1:
        raise TypeError("verified economic epoch handle type is not closed")
    with _VERIFIED_ECONOMIC_EPOCH_AUTHORITY_LOCK:
        authority = _VERIFIED_ECONOMIC_EPOCH_AUTHORITIES.get(witness)
    if authority is None:
        raise TypeError("verified economic epoch handle is not verifier-registered")
    return authority


def _verified_economic_epoch_prepared_v1(
    witness: VerifiedEconomicEpochV1,
) -> PreparedEconomicEpochV1:
    return _verified_economic_epoch_authority_v1(witness).prepared


def _snapshot_verified_economic_epoch_v1(
    witness: VerifiedEconomicEpochV1,
) -> VerifiedEconomicEpochV1:
    """Return a fresh handle derived only from the shell-owned authority record."""

    authority = _verified_economic_epoch_authority_v1(witness)
    return VerifiedEconomicEpochV1(
        _VERIFIED_ECONOMIC_EPOCH_TOKEN,
        authority,
    )


def _verified_economic_epoch_is_bound_to_publisher_v1(
    witness: VerifiedEconomicEpochV1,
    publisher_binding_token: object,
    receipt_verifier: SuccinctReceiptVerifierV1,
) -> bool:
    """Return whether a witness was verified by this exact publisher instance."""

    if type(publisher_binding_token) is not object:
        raise TypeError("publisher binding token must be an exact opaque object")
    authority = _verified_economic_epoch_authority_v1(witness)
    return (
        authority.publisher_binding_token is publisher_binding_token
        and authority.publisher_verifier_identity is receipt_verifier
    )


def verify_economic_epoch_v1(
    candidate: EconomicEpochReceiptCandidateV1,
    receipt_verifier: SuccinctReceiptVerifierV1,
) -> VerifiedEconomicEpochV1:
    """Verify one epoch for research, replay, and differential inspection.

    The caller supplies the cryptographic verifier, so this witness carries no
    publication binding. A GlobalEconomicCommitPortV1 rejects it. Production
    admission must use the verifier retained by the publisher instance.
    """

    return _verify_economic_epoch_with_publisher_binding_v1(
        candidate,
        receipt_verifier,
        publisher_binding_token=None,
        publisher_verifier_identity=None,
    )


def _verify_economic_epoch_for_publisher_v1(
    candidate: EconomicEpochReceiptCandidateV1,
    receipt_verifier: SuccinctReceiptVerifierV1,
    publisher_binding_token: object,
) -> VerifiedEconomicEpochV1:
    """Verify one epoch with the backend selected by an exact publisher."""

    if type(publisher_binding_token) is not object:
        raise TypeError("publisher binding token must be an exact opaque object")
    return _verify_economic_epoch_with_publisher_binding_v1(
        candidate,
        receipt_verifier,
        publisher_binding_token=publisher_binding_token,
        publisher_verifier_identity=receipt_verifier,
    )


def _execute_prepared_economic_epoch_v1(
    prepared: PreparedEconomicEpochV1,
    receipt_verifier: SuccinctReceiptVerifierV1,
) -> PreparedEconomicEpochV1:
    """Execute exactly the prepared receipt, image and journal on the verifier.

    A detached preparer-constructed copy is fixed before I/O.  Subclasses,
    forged instances and substituted field records are refused while making
    that copy, before any call.  The returned copy is the only subject that may
    reach final witness minting, so callback-side mutation of the caller-held
    prepared object cannot relabel the verified result.  The generic port's
    return value is ignored, as before this extraction; the measured Bound
    verifier enforces its own exact-None contract internally.
    """

    owned_prepared = _snapshot_prepared_economic_epoch_v1(prepared)
    fields = _require_prepared_economic_epoch_v1(owned_prepared)
    receipt_verifier.verify_succinct_receipt(
        fields.receipt_bytes,
        expected_image_id=fields.expected_image_id,
        expected_journal_bytes=fields.expected_journal_bytes,
    )
    return owned_prepared


def _verify_economic_epoch_with_publisher_binding_v1(
    candidate: EconomicEpochReceiptCandidateV1,
    receipt_verifier: SuccinctReceiptVerifierV1,
    *,
    publisher_binding_token: object | None,
    publisher_verifier_identity: object | None,
) -> VerifiedEconomicEpochV1:
    """Prepare in core, execute the exact subject, then mint the retained result.

    ``prepare_economic_epoch_v1`` snapshots the candidate before any guard, so
    ``prepared`` is detached from the caller's graph before I/O starts and a
    verifier callback that mutates caller values cannot relabel the minted
    witness.  Nothing is registered when preparation or the verifier raises.
    """

    prepared = prepare_economic_epoch_v1(candidate)
    prepared = _execute_prepared_economic_epoch_v1(prepared, receipt_verifier)
    return VerifiedEconomicEpochV1(
        _VERIFIED_ECONOMIC_EPOCH_TOKEN,
        _VerifiedEconomicEpochAuthorityRecordV1(
            prepared=prepared,
            publisher_binding_token=publisher_binding_token,
            publisher_verifier_identity=publisher_verifier_identity,
        ),
    )


__all__ = [
    "SuccinctReceiptVerifierV1",
    "VerifiedEconomicEpochV1",
    "verify_economic_epoch_v1",
]
