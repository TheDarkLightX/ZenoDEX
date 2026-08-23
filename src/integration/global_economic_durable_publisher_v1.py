"""Verifier-owned durable publication boundary for ordinary economic epochs.

This unmounted adapter fixes one genesis activation, receipt verifier, profile,
and SQLite journal for its full lifetime.  It verifies an epoch, derives the
publication record and complete byte bundle internally, and uses the journal's
compare-and-swap transaction as the sole durable linearization point.

It grants no production writer, settlement, consensus, finality, migration, or
external-delivery authority.  Its receipt assurance is exactly the assurance
provided by the verifier instance selected at construction.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from threading import Lock

from ..core.economic_initial_state_publisher_verification_v1 import (
    _verify_economic_initial_state_for_publisher_v1,
)
from ..core.economic_initial_state_v1 import EconomicInitialStateAdmissionV1
from ..core.economic_receipt_verifier_deployment_v1 import (
    BoundEconomicReceiptVerifierV1,
)
from ..core.economic_receipt_verifier_registry_v1 import (
    EconomicReceiptVerifierSelectionPurposeV1,
)
from ..core.global_economic_authority_head_v1 import (
    GlobalEconomicAuthorityHeadV1,
    GlobalEconomicAuthorityStatusV1,
)
from ..core.global_economic_durable_activation_v1 import (
    DurableEconomicInitialStateBundleV1,
    prepare_durable_economic_initial_state_bundle_v1,
)
from ..core.global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from ..core.global_economic_proof_v1 import (
    EconomicEpochReceiptCandidateV1,
    _snapshot_economic_epoch_candidate_v1,
    _snapshot_verified_economic_epoch_v1,
    _verified_economic_epoch_is_bound_to_publisher_v1,
    _verify_economic_epoch_for_publisher_v1,
)
from ..core.global_economic_refinement_snapshot_v1 import _snapshot_state_v1
from ..core.global_settlement_types_v1 import (
    EconomicProfileSnapshotV1,
    GlobalEconomicStateV1,
    ProfileStatusV1,
    canonical_global_bytes_v1,
)
from .global_economic_authority_journal_v1 import (
    _create_or_recover_authority_for_publisher_v1,
    authority_journal_path_for_epoch_v1,
    economic_epoch_store_root_v1,
)
from .global_economic_commit_v1 import (
    EconomicEpochBodyAndStateV1,
    PublishedEconomicEpochV1,
    _build_published_economic_epoch_v1,
    _economic_epoch_binding_rejection_reason_v1,
    _snapshot_body_and_state_v1,
)
from .global_economic_durable_epoch_v1 import (
    DurableEconomicEpochMaterialV1,
    DurableEconomicPublicationHeadV1,
    prepare_durable_economic_epoch_bundle_v1,
)
from .global_economic_epoch_journal_v1 import (
    DurableEconomicEpochCommitOutcomeV1,
    DurableEconomicEpochCommitStatusV1,
    DurableEconomicEpochWriteCapabilityV1,
    GlobalEconomicEpochJournalV1,
    _create_epoch_journal_for_verified_publisher_v1,
    _open_epoch_journal_for_verified_publisher_v1,
    _require_write_capability_v1,
)

_DURABLE_PUBLISHER_MINT_V1 = object()


@dataclass(frozen=True, slots=True)
class VerifiedDurableEconomicPublishOutcomeV1:
    """Typed result of one verifier-owned durable publication attempt."""

    status: DurableEconomicEpochCommitStatusV1
    head: DurableEconomicPublicationHeadV1
    committed_epoch: DurableEconomicPublicationHeadV1 | None = None
    published_epoch: PublishedEconomicEpochV1 | None = None

    def __post_init__(self) -> None:
        if type(self.status) is not DurableEconomicEpochCommitStatusV1:
            raise TypeError("durable publisher outcome status is not closed")
        if type(self.head) is not DurableEconomicPublicationHeadV1:
            raise TypeError("durable publisher outcome head is not closed")
        successful = {
            DurableEconomicEpochCommitStatusV1.COMMITTED,
            DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED,
        }
        if self.status in successful:
            if type(self.committed_epoch) is not DurableEconomicPublicationHeadV1:
                raise TypeError("durable publisher success lacks committed epoch")
            if type(self.published_epoch) is not PublishedEconomicEpochV1:
                raise TypeError("durable publisher success lacks published record")
        elif self.committed_epoch is not None or self.published_epoch is not None:
            raise ValueError("durable publisher no-effect outcome declares publication")


@dataclass(frozen=True, slots=True)
class _VerifiedActivationV1:
    profile: EconomicProfileSnapshotV1
    state: GlobalEconomicStateV1
    certificate_root: str
    bundle: DurableEconomicInitialStateBundleV1


def _snapshot_publication_head_v1(
    head: DurableEconomicPublicationHeadV1,
) -> DurableEconomicPublicationHeadV1:
    if type(head) is not DurableEconomicPublicationHeadV1:
        raise TypeError("durable publisher expected source type is not closed")
    return DurableEconomicPublicationHeadV1(
        publication_id=head.publication_id,
        sequence=head.sequence,
        activation_id=head.activation_id,
        chain_id=head.chain_id,
        deployment_root=head.deployment_root,
        profile_root=head.profile_root,
        writer_epoch=head.writer_epoch,
        height=head.height,
        state_root=head.state_root,
        commit_id=head.commit_id,
        certificate_root=head.certificate_root,
    )


def _same_publication_head_v1(
    left: DurableEconomicPublicationHeadV1,
    right: DurableEconomicPublicationHeadV1,
) -> bool:
    return (
        left.publication_id,
        left.sequence,
        left.activation_id,
        left.chain_id,
        left.deployment_root,
        left.profile_root,
        left.writer_epoch,
        left.height,
        left.state_root,
        left.commit_id,
        left.certificate_root,
    ) == (
        right.publication_id,
        right.sequence,
        right.activation_id,
        right.chain_id,
        right.deployment_root,
        right.profile_root,
        right.writer_epoch,
        right.height,
        right.state_root,
        right.commit_id,
        right.certificate_root,
    )


def _prepare_verified_activation_v1(
    admission: EconomicInitialStateAdmissionV1,
    receipt_verifier: BoundEconomicReceiptVerifierV1,
) -> _VerifiedActivationV1:
    if type(admission) is not EconomicInitialStateAdmissionV1:
        raise TypeError("durable publisher requires exact initial-state admission")
    if type(receipt_verifier) is not BoundEconomicReceiptVerifierV1:
        raise TypeError(
            "durable publisher requires a bound economic receipt verifier"
        )
    admission_profile = snapshot_economic_profile_v1(admission.profile)
    admission_state = _snapshot_state_v1(admission.state)
    receipt_verifier.require_binding(
        verifier_registry_root=admission_profile.verifier_registry_root,
        deployment_root=admission_state.deployment_root,
        profile_root=admission_profile.profile_id,
        root_image_id=admission_profile.root_image_id,
        selection_purpose=(
            EconomicReceiptVerifierSelectionPurposeV1.RESEARCH_SHADOW
        ),
    )
    verified = _verify_economic_initial_state_for_publisher_v1(
        admission,
        receipt_verifier,
    )
    profile = snapshot_economic_profile_v1(verified.profile)
    state = _snapshot_state_v1(verified.state)
    if profile.status is not ProfileStatusV1.ACTIVE:
        raise ValueError("durable publisher genesis profile must be active")
    receipt_verifier.require_binding(
        verifier_registry_root=profile.verifier_registry_root,
        deployment_root=state.deployment_root,
        profile_root=profile.profile_id,
        root_image_id=profile.root_image_id,
        selection_purpose=(
            EconomicReceiptVerifierSelectionPurposeV1.RESEARCH_SHADOW
        ),
    )
    bundle = prepare_durable_economic_initial_state_bundle_v1(
        admission,
        source_head=None,
    )
    head = bundle.head
    bindings = (
        (head.chain_id, state.chain_id),
        (head.deployment_root, state.deployment_root),
        (head.profile_root, profile.profile_id),
        (head.state_root, state.state_root),
        (head.writer_epoch, state.writer_epoch),
        (head.writer_epoch, profile.authority_epoch),
        (head.height, state.height),
        (head.certificate_root, verified.certificate_root),
    )
    if any(actual != expected for actual, expected in bindings):
        raise ValueError("durable publisher verified activation binding mismatch")
    return _VerifiedActivationV1(
        profile=profile,
        state=state,
        certificate_root=verified.certificate_root,
        bundle=bundle,
    )


def _build_initial_authority_v1(
    bundle: DurableEconomicInitialStateBundleV1,
    profile: EconomicProfileSnapshotV1,
    state: GlobalEconomicStateV1,
    receipt_verifier: BoundEconomicReceiptVerifierV1,
    epoch_path: str | Path,
) -> GlobalEconomicAuthorityHeadV1:
    return GlobalEconomicAuthorityHeadV1(
        generation=bundle.record.generation,
        activation_id=bundle.record.activation_id,
        chain_id=state.chain_id,
        deployment_root=state.deployment_root,
        epoch_store_root=economic_epoch_store_root_v1(epoch_path),
        profile_root=profile.profile_id,
        writer_epoch=state.writer_epoch,
        verifier_registry_root=profile.verifier_registry_root,
        verifier_release_id=receipt_verifier.release_id,
        verifier_binding_root=receipt_verifier.binding_root,
        root_image_id=profile.root_image_id,
        status=GlobalEconomicAuthorityStatusV1.ACTIVE,
    )


def _require_candidate_source_v1(
    *,
    source: DurableEconomicPublicationHeadV1,
    activation_id: str,
    profile: EconomicProfileSnapshotV1,
    candidate: EconomicEpochReceiptCandidateV1,
    body: EconomicEpochBodyAndStateV1,
) -> None:
    pre_state = candidate.pre_state
    certificate = candidate.certificate
    bindings = (
        (source.activation_id, activation_id, "activation"),
        (source.profile_root, profile.profile_id, "source profile"),
        (source.writer_epoch, profile.authority_epoch, "source writer epoch"),
        (pre_state.chain_id, source.chain_id, "pre-state chain"),
        (pre_state.deployment_root, source.deployment_root, "pre-state deployment"),
        (pre_state.profile_root, source.profile_root, "pre-state profile"),
        (pre_state.writer_epoch, source.writer_epoch, "pre-state writer epoch"),
        (pre_state.height, source.height, "pre-state height"),
        (pre_state.state_root, source.state_root, "pre-state root"),
        (body.pre_state_root, source.state_root, "body pre-state root"),
        (certificate.pre_state_root, source.state_root, "certificate pre-state root"),
    )
    for actual, expected, label in bindings:
        if actual != expected:
            raise ValueError(f"durable publisher {label} mismatch")


def _stale_outcome_v1(
    head: DurableEconomicPublicationHeadV1,
) -> VerifiedDurableEconomicPublishOutcomeV1:
    return VerifiedDurableEconomicPublishOutcomeV1(
        status=DurableEconomicEpochCommitStatusV1.STALE_HEAD,
        head=head,
    )


class VerifiedDurableEconomicPublisherV1:
    """Sealed unmounted verifier-to-SQLite publication capability."""

    __slots__ = (
        "__activation_id",
        "__binding_token",
        "__journal",
        "__lock",
        "__profile",
        "__receipt_verifier",
        "__receipt_verifier_binding_root",
        "__receipt_verifier_release_id",
        "__sealed",
        "__write_capability",
    )
    __activation_id: str
    __binding_token: object
    __journal: GlobalEconomicEpochJournalV1
    __lock: Lock
    __profile: EconomicProfileSnapshotV1
    __receipt_verifier: BoundEconomicReceiptVerifierV1
    __receipt_verifier_binding_root: str
    __receipt_verifier_release_id: str
    __sealed: bool
    __write_capability: DurableEconomicEpochWriteCapabilityV1

    def __init__(
        self,
        mint: object,
        journal: GlobalEconomicEpochJournalV1,
        write_capability: DurableEconomicEpochWriteCapabilityV1,
        profile: EconomicProfileSnapshotV1,
        receipt_verifier: BoundEconomicReceiptVerifierV1,
        activation_id: str,
    ) -> None:
        if mint is not _DURABLE_PUBLISHER_MINT_V1:
            raise TypeError("durable publisher is factory-constructed")
        if type(journal) is not GlobalEconomicEpochJournalV1:
            raise TypeError("durable publisher journal type is not closed")
        _require_write_capability_v1(journal, write_capability)
        object.__setattr__(self, "_VerifiedDurableEconomicPublisherV1__journal", journal)
        object.__setattr__(
            self,
            "_VerifiedDurableEconomicPublisherV1__write_capability",
            write_capability,
        )
        object.__setattr__(
            self,
            "_VerifiedDurableEconomicPublisherV1__profile",
            snapshot_economic_profile_v1(profile),
        )
        object.__setattr__(
            self,
            "_VerifiedDurableEconomicPublisherV1__receipt_verifier",
            receipt_verifier,
        )
        object.__setattr__(
            self,
            "_VerifiedDurableEconomicPublisherV1__receipt_verifier_binding_root",
            receipt_verifier.binding_root,
        )
        object.__setattr__(
            self,
            "_VerifiedDurableEconomicPublisherV1__receipt_verifier_release_id",
            receipt_verifier.release_id,
        )
        object.__setattr__(
            self,
            "_VerifiedDurableEconomicPublisherV1__activation_id",
            activation_id,
        )
        object.__setattr__(
            self,
            "_VerifiedDurableEconomicPublisherV1__binding_token",
            object(),
        )
        object.__setattr__(
            self,
            "_VerifiedDurableEconomicPublisherV1__lock",
            Lock(),
        )
        object.__setattr__(self, "_VerifiedDurableEconomicPublisherV1__sealed", True)

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_VerifiedDurableEconomicPublisherV1__sealed", False):
            raise TypeError("durable publisher selection is immutable")
        object.__setattr__(self, name, value)

    @classmethod
    def create(
        cls,
        path: str | Path,
        initial_state_admission: EconomicInitialStateAdmissionV1,
        receipt_verifier: BoundEconomicReceiptVerifierV1,
    ) -> VerifiedDurableEconomicPublisherV1:
        verified = _prepare_verified_activation_v1(
            initial_state_admission,
            receipt_verifier,
        )
        authority = _build_initial_authority_v1(
            verified.bundle,
            verified.profile,
            verified.state,
            receipt_verifier,
            path,
        )
        authority_path = authority_journal_path_for_epoch_v1(path)
        _create_or_recover_authority_for_publisher_v1(
            authority_path,
            authority,
        )
        journal, write_capability = (
            _create_epoch_journal_for_verified_publisher_v1(
                path,
                verified.bundle,
                authority_path,
                authority,
            )
        )
        return cls(
            _DURABLE_PUBLISHER_MINT_V1,
            journal,
            write_capability,
            verified.profile,
            receipt_verifier,
            verified.bundle.record.activation_id,
        )

    @classmethod
    def open(
        cls,
        path: str | Path,
        initial_state_admission: EconomicInitialStateAdmissionV1,
        receipt_verifier: BoundEconomicReceiptVerifierV1,
    ) -> VerifiedDurableEconomicPublisherV1:
        verified = _prepare_verified_activation_v1(
            initial_state_admission,
            receipt_verifier,
        )
        authority = _build_initial_authority_v1(
            verified.bundle,
            verified.profile,
            verified.state,
            receipt_verifier,
            path,
        )
        authority_path = authority_journal_path_for_epoch_v1(path)
        journal, write_capability = _open_epoch_journal_for_verified_publisher_v1(
            path,
            authority_path,
            authority,
        )
        try:
            if (
                journal.activation_bundle.canonical_bytes
                != verified.bundle.canonical_bytes
            ):
                raise ValueError("durable publisher activation bundle mismatch")
            journal._require_current_authority_v1()
            return cls(
                _DURABLE_PUBLISHER_MINT_V1,
                journal,
                write_capability,
                verified.profile,
                receipt_verifier,
                verified.bundle.record.activation_id,
            )
        except BaseException:
            journal.close()
            raise

    def __enter__(self) -> VerifiedDurableEconomicPublisherV1:
        _ = self.head
        return self

    def __exit__(self, exc_type: object, exc: object, traceback: object) -> None:
        self.close()

    @property
    def profile(self) -> EconomicProfileSnapshotV1:
        with self.__lock:
            return snapshot_economic_profile_v1(self.__profile)

    @property
    def head(self) -> DurableEconomicPublicationHeadV1:
        with self.__lock:
            return self.__journal.head

    def close(self) -> None:
        with self.__lock:
            self.__journal.close()

    def publish_economic_epoch(
        self,
        *,
        expected_source: DurableEconomicPublicationHeadV1,
        candidate: EconomicEpochReceiptCandidateV1,
        body_and_state: EconomicEpochBodyAndStateV1,
    ) -> VerifiedDurableEconomicPublishOutcomeV1:
        """Verify and atomically persist one exact complete epoch bundle."""

        source = _snapshot_publication_head_v1(expected_source)
        if type(candidate) is not EconomicEpochReceiptCandidateV1:
            raise TypeError("durable publisher epoch candidate type is not closed")
        owned_candidate = _snapshot_economic_epoch_candidate_v1(candidate)
        owned_body = _snapshot_body_and_state_v1(body_and_state)

        with self.__lock:
            selected_profile = snapshot_economic_profile_v1(self.__profile)
            if selected_profile.status is not ProfileStatusV1.ACTIVE:
                raise ValueError("durable publisher profile is not active")
            if canonical_global_bytes_v1(owned_candidate.profile) != (
                canonical_global_bytes_v1(selected_profile)
            ):
                raise ValueError("durable publisher candidate profile is not selected")

            stored_source = self.__journal.publication_head(source.publication_id)
            if stored_source is None or not _same_publication_head_v1(
                stored_source,
                source,
            ):
                return _stale_outcome_v1(self.__journal.head)
            _require_candidate_source_v1(
                source=source,
                activation_id=self.__activation_id,
                profile=selected_profile,
                candidate=owned_candidate,
                body=owned_body,
            )

            cas_token = self.__journal.acquire_cas_head_token()
            receipt_verifier = self.__receipt_verifier
            receipt_verifier_binding_root = self.__receipt_verifier_binding_root
            receipt_verifier_release_id = self.__receipt_verifier_release_id
            binding_token = self.__binding_token
            verified = _verify_economic_epoch_for_publisher_v1(
                owned_candidate,
                receipt_verifier,
                binding_token,
            )
            if (
                self.__receipt_verifier is not receipt_verifier
                or self.__receipt_verifier_binding_root
                != receipt_verifier_binding_root
                or self.__receipt_verifier_release_id
                != receipt_verifier_release_id
                or receipt_verifier.binding_root != receipt_verifier_binding_root
                or receipt_verifier.release_id != receipt_verifier_release_id
                or self.__binding_token is not binding_token
                or canonical_global_bytes_v1(self.__profile)
                != canonical_global_bytes_v1(selected_profile)
            ):
                raise ValueError(
                    "durable publisher verifier selection changed during verification"
                )
            if not _verified_economic_epoch_is_bound_to_publisher_v1(
                verified,
                binding_token,
                receipt_verifier,
            ):
                raise TypeError("durable publisher verifier binding is absent")
            owned_verified = _snapshot_verified_economic_epoch_v1(verified)
            rejection = _economic_epoch_binding_rejection_reason_v1(
                profile=selected_profile,
                pre_state=owned_candidate.pre_state,
                verified_epoch=owned_verified,
                body_and_state=owned_body,
            )
            if rejection is not None:
                raise ValueError(f"durable publisher binding rejected: {rejection}")

            published = _build_published_economic_epoch_v1(
                profile=selected_profile,
                verified_epoch=owned_verified,
                body_and_state=owned_body,
            )
            bundle = prepare_durable_economic_epoch_bundle_v1(
                DurableEconomicEpochMaterialV1(
                    source_head=source,
                    profile=selected_profile,
                    certificate=owned_verified.certificate,
                    effect_plan=owned_verified.effect_plan,
                    body_and_state=owned_body,
                    published_epoch=published,
                    receipt_bytes=owned_candidate.receipt_bytes,
                )
            )
            journal_outcome = (
                self.__journal._commit_epoch_from_verified_publisher_v1(
                    bundle,
                    cas_token,
                    self.__write_capability,
                )
            )
            return self._outcome_v1(journal_outcome, published)

    @staticmethod
    def _outcome_v1(
        outcome: DurableEconomicEpochCommitOutcomeV1,
        published: PublishedEconomicEpochV1,
    ) -> VerifiedDurableEconomicPublishOutcomeV1:
        successful = {
            DurableEconomicEpochCommitStatusV1.COMMITTED,
            DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED,
        }
        return VerifiedDurableEconomicPublishOutcomeV1(
            status=outcome.status,
            head=outcome.head,
            committed_epoch=outcome.committed_epoch,
            published_epoch=published if outcome.status in successful else None,
        )


__all__ = [
    "VerifiedDurableEconomicPublishOutcomeV1",
    "VerifiedDurableEconomicPublisherV1",
]
