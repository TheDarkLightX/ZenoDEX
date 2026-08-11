"""Atomic in-memory conformance shell for verified economic epochs.

This adapter models one compare-and-swap publication capability.  It retains
state, the exact verified certificate, replay identity, receipt lineage, and
external outbox rows under one lock.  It does not provide durable storage,
crash recovery, consensus finality, or production writer authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from threading import Lock
from typing import Mapping

from ..core.global_economic_proof_v1 import VerifiedEconomicEpochV1
from ..core.global_settlement_types_v1 import (
    MAX_EPOCH_COMMANDS_V1,
    EconomicProfileSnapshotV1,
    GlobalEconomicStateV1,
    ProfileStatusV1,
    _require_root,
    _require_semantic_order_unique,
    hash_global_v1,
    validate_global_state_profile_v1,
)


@dataclass(frozen=True, slots=True)
class EconomicEpochBodyAndStateV1:
    pre_state_root: str
    post_state: GlobalEconomicStateV1
    ordered_command_body_hashes: tuple[str, ...]
    receipt_archive_root: str
    data_availability_root: str
    finality_root: str

    def __post_init__(self) -> None:
        _require_root(self.pre_state_root, name="epoch body pre-state root")
        if not isinstance(self.post_state, GlobalEconomicStateV1):
            raise TypeError("epoch body post-state is invalid")
        hashes = _require_semantic_order_unique(
            self.ordered_command_body_hashes,
            name="epoch body command hashes",
        )
        if not 1 <= len(hashes) <= MAX_EPOCH_COMMANDS_V1:
            raise ValueError("epoch body requires between one and 64 commands")
        for index, command_hash in enumerate(hashes):
            _require_root(command_hash, name=f"epoch body command hash[{index}]")
        _require_root(self.receipt_archive_root, name="epoch body receipt archive root")
        _require_root(self.data_availability_root, name="epoch body data availability root")
        _require_root(self.finality_root, name="epoch body finality root")

    @property
    def body_commitment(self) -> str:
        return hash_global_v1(
            "global-economic-epoch-body-v1",
            {
                "pre_state_root": self.pre_state_root,
                "post_state_root": self.post_state.state_root,
                "ordered_command_body_hashes": self.ordered_command_body_hashes,
                "receipt_archive_root": self.receipt_archive_root,
                "outbox": self.post_state.outbox,
            },
        )

    def to_canonical(self) -> Mapping[str, object]:
        return {
            "pre_state_root": self.pre_state_root,
            "post_state": self.post_state,
            "ordered_command_body_hashes": self.ordered_command_body_hashes,
            "receipt_archive_root": self.receipt_archive_root,
            "data_availability_root": self.data_availability_root,
            "finality_root": self.finality_root,
        }


class CommitOutcomeStatusV1(str, Enum):
    COMMITTED = "COMMITTED"
    ALREADY_COMMITTED = "ALREADY_COMMITTED"
    STALE_HEAD = "STALE_HEAD"
    PROFILE_MISMATCH = "PROFILE_MISMATCH"
    BINDING_REJECTED = "BINDING_REJECTED"


@dataclass(frozen=True, slots=True)
class PublishedEconomicEpochV1:
    commit_id: str
    certificate_root: str
    profile_root: str
    writer_epoch: int
    pre_state_root: str
    post_state_root: str
    body_commitment: str
    data_availability_root: str
    finality_root: str
    receipt_root: str
    receipt_archive_root: str
    effect_plan_root: str
    release_observation_root: str

    def __post_init__(self) -> None:
        for field_name in (
            "commit_id",
            "certificate_root",
            "profile_root",
            "pre_state_root",
            "post_state_root",
            "body_commitment",
            "data_availability_root",
            "finality_root",
            "receipt_root",
            "receipt_archive_root",
            "effect_plan_root",
            "release_observation_root",
        ):
            _require_root(getattr(self, field_name), name=f"published epoch {field_name}")
        if type(self.writer_epoch) is not int or self.writer_epoch < 0:
            raise ValueError("published epoch writer_epoch must be a non-negative integer")

    def to_canonical(self) -> Mapping[str, object]:
        return {
            "commit_id": self.commit_id,
            "certificate_root": self.certificate_root,
            "profile_root": self.profile_root,
            "writer_epoch": self.writer_epoch,
            "pre_state_root": self.pre_state_root,
            "post_state_root": self.post_state_root,
            "body_commitment": self.body_commitment,
            "data_availability_root": self.data_availability_root,
            "finality_root": self.finality_root,
            "receipt_root": self.receipt_root,
            "receipt_archive_root": self.receipt_archive_root,
            "effect_plan_root": self.effect_plan_root,
            "release_observation_root": self.release_observation_root,
        }


@dataclass(frozen=True, slots=True)
class CommitOutcomeV1:
    status: CommitOutcomeStatusV1
    state: GlobalEconomicStateV1
    commit_id: str
    record: PublishedEconomicEpochV1 | None = None
    reason: str | None = None


class GlobalEconomicCommitPortV1:
    """Reference unique publication capability for one active profile."""

    def __init__(
        self,
        profile: EconomicProfileSnapshotV1,
        initial_state: GlobalEconomicStateV1,
    ) -> None:
        if profile.status is not ProfileStatusV1.ACTIVE:
            raise ValueError("commit port requires an ACTIVE economic profile")
        validate_global_state_profile_v1(initial_state, profile)
        self._profile = profile
        self._state = initial_state
        self._records: dict[str, PublishedEconomicEpochV1] = {}
        self._lock = Lock()

    @property
    def profile(self) -> EconomicProfileSnapshotV1:
        return self._profile

    @property
    def state(self) -> GlobalEconomicStateV1:
        with self._lock:
            return self._state

    @property
    def records(self) -> tuple[PublishedEconomicEpochV1, ...]:
        with self._lock:
            return tuple(self._records[key] for key in sorted(self._records))

    def commit_verified_economic_epoch(
        self,
        *,
        expected_head: str,
        expected_profile: str,
        verified_epoch: VerifiedEconomicEpochV1,
        body_and_state: EconomicEpochBodyAndStateV1,
    ) -> CommitOutcomeV1:
        """Atomically publish the exact verified epoch tuple or a typed no-op."""

        _require_root(expected_head, name="commit expected head")
        _require_root(expected_profile, name="commit expected profile")
        if not isinstance(verified_epoch, VerifiedEconomicEpochV1):
            raise TypeError("commit requires VerifiedEconomicEpochV1")
        if not isinstance(body_and_state, EconomicEpochBodyAndStateV1):
            raise TypeError("commit body_and_state is invalid")
        with self._lock:
            return self._commit_locked(
                expected_head=expected_head,
                expected_profile=expected_profile,
                verified_epoch=verified_epoch,
                body_and_state=body_and_state,
            )

    def _commit_locked(
        self,
        *,
        expected_head: str,
        expected_profile: str,
        verified_epoch: VerifiedEconomicEpochV1,
        body_and_state: EconomicEpochBodyAndStateV1,
    ) -> CommitOutcomeV1:
        commit_id = verified_epoch.commit_id
        if expected_profile != self._profile.profile_id:
            return self._reject(CommitOutcomeStatusV1.PROFILE_MISMATCH, commit_id, "expected profile is inactive")
        previous = self._records.get(commit_id)
        if previous is not None:
            if expected_head != previous.pre_state_root:
                return self._reject(CommitOutcomeStatusV1.STALE_HEAD, commit_id, "expected head is stale")
            replay_reason = self._committed_replay_binding_rejection_reason(
                previous,
                verified_epoch,
                body_and_state,
            )
            if replay_reason is not None:
                return self._reject(CommitOutcomeStatusV1.BINDING_REJECTED, commit_id, replay_reason)
            return CommitOutcomeV1(
                CommitOutcomeStatusV1.ALREADY_COMMITTED,
                self._state,
                commit_id,
                record=previous,
            )
        if expected_head != self._state.state_root:
            return self._reject(CommitOutcomeStatusV1.STALE_HEAD, commit_id, "expected head is stale")
        reason = self._binding_rejection_reason(verified_epoch, body_and_state)
        if reason is not None:
            return self._reject(CommitOutcomeStatusV1.BINDING_REJECTED, commit_id, reason)
        certificate = verified_epoch.certificate
        record = PublishedEconomicEpochV1(
            commit_id=commit_id,
            certificate_root=certificate.certificate_root,
            profile_root=certificate.profile_root,
            writer_epoch=certificate.writer_epoch,
            pre_state_root=certificate.pre_state_root,
            post_state_root=certificate.post_state_root,
            body_commitment=certificate.body_commitment,
            data_availability_root=certificate.data_availability_root,
            finality_root=certificate.finality_root,
            receipt_root=certificate.receipt_root,
            receipt_archive_root=body_and_state.receipt_archive_root,
            effect_plan_root=verified_epoch.effect_plan.effect_plan_root,
            release_observation_root=hash_global_v1(
                "global-economic-release-observation-v1",
                {
                    "profile_root": self._profile.profile_id,
                    "lane_registry_root": self._profile.lane_registry.registry_root,
                    "route_registry_root": self._profile.route_registry.registry_root,
                },
            ),
        )
        self._state = body_and_state.post_state
        self._records[commit_id] = record
        return CommitOutcomeV1(
            CommitOutcomeStatusV1.COMMITTED,
            self._state,
            commit_id,
            record=record,
        )

    def _binding_rejection_reason(
        self,
        verified_epoch: VerifiedEconomicEpochV1,
        body_and_state: EconomicEpochBodyAndStateV1,
    ) -> str | None:
        certificate = verified_epoch.certificate
        post_state = body_and_state.post_state
        try:
            validate_global_state_profile_v1(post_state, self._profile)
        except ValueError as exc:
            return str(exc)
        bindings = (
            (certificate.chain_id, self._state.chain_id, "certificate chain"),
            (certificate.deployment_root, self._state.deployment_root, "certificate deployment"),
            (certificate.profile_root, self._profile.profile_id, "certificate profile"),
            (certificate.writer_epoch, self._profile.authority_epoch, "writer epoch"),
            (certificate.pre_state_root, self._state.state_root, "pre-state root"),
            (body_and_state.pre_state_root, self._state.state_root, "body pre-state root"),
            (certificate.post_state_root, post_state.state_root, "post-state root"),
            (certificate.body_commitment, body_and_state.body_commitment, "body commitment"),
            (certificate.data_availability_root, body_and_state.data_availability_root, "data availability root"),
            (certificate.finality_root, body_and_state.finality_root, "finality root"),
            (post_state.profile_root, self._profile.profile_id, "post-state profile"),
            (post_state.writer_epoch, self._profile.authority_epoch, "post-state writer epoch"),
            (post_state.chain_id, self._state.chain_id, "post-state chain"),
            (post_state.deployment_root, self._state.deployment_root, "post-state deployment"),
            (post_state.height, certificate.height, "post-state height"),
        )
        for actual, expected, label in bindings:
            if actual != expected:
                return f"{label} mismatch"
        if certificate.height != self._state.height + 1:
            return "economic epoch height must advance exactly once"
        if len(body_and_state.ordered_command_body_hashes) != len(certificate.ordered_occurrence_ids):
            return "body command count does not match verified occurrences"
        return None

    def _committed_replay_binding_rejection_reason(
        self,
        previous: PublishedEconomicEpochV1,
        verified_epoch: VerifiedEconomicEpochV1,
        body_and_state: EconomicEpochBodyAndStateV1,
    ) -> str | None:
        """Require an already-committed retry to carry the original tuple."""

        certificate = verified_epoch.certificate
        try:
            validate_global_state_profile_v1(body_and_state.post_state, self._profile)
        except ValueError as exc:
            return str(exc)
        bindings = (
            (certificate.certificate_root, previous.certificate_root, "certificate root"),
            (certificate.profile_root, previous.profile_root, "certificate profile"),
            (certificate.writer_epoch, previous.writer_epoch, "writer epoch"),
            (certificate.pre_state_root, previous.pre_state_root, "certificate pre-state root"),
            (certificate.post_state_root, previous.post_state_root, "certificate post-state root"),
            (certificate.body_commitment, previous.body_commitment, "certificate body commitment"),
            (certificate.data_availability_root, previous.data_availability_root, "certificate data availability root"),
            (certificate.finality_root, previous.finality_root, "certificate finality root"),
            (certificate.receipt_root, previous.receipt_root, "certificate receipt root"),
            (verified_epoch.receipt_digest, previous.receipt_root, "receipt digest"),
            (verified_epoch.effect_plan.effect_plan_root, previous.effect_plan_root, "effect plan root"),
            (body_and_state.pre_state_root, previous.pre_state_root, "body pre-state root"),
            (body_and_state.post_state.state_root, previous.post_state_root, "body post-state root"),
            (body_and_state.data_availability_root, previous.data_availability_root, "data availability root"),
            (body_and_state.finality_root, previous.finality_root, "finality root"),
            (body_and_state.receipt_archive_root, previous.receipt_archive_root, "receipt archive root"),
            (body_and_state.body_commitment, previous.body_commitment, "body commitment"),
        )
        for actual, expected, label in bindings:
            if actual != expected:
                return f"{label} mismatch"
        return None

    def _reject(
        self,
        status: CommitOutcomeStatusV1,
        commit_id: str,
        reason: str,
    ) -> CommitOutcomeV1:
        return CommitOutcomeV1(status, self._state, commit_id, reason=reason)


def commit_verified_economic_epoch_v1(
    port: GlobalEconomicCommitPortV1,
    *,
    expected_head: str,
    expected_profile: str,
    verified_epoch: VerifiedEconomicEpochV1,
    body_and_state: EconomicEpochBodyAndStateV1,
) -> CommitOutcomeV1:
    """Functional facade matching the GlobalSettlementABI publication name."""

    if not isinstance(port, GlobalEconomicCommitPortV1):
        raise TypeError("port must be GlobalEconomicCommitPortV1")
    return port.commit_verified_economic_epoch(
        expected_head=expected_head,
        expected_profile=expected_profile,
        verified_epoch=verified_epoch,
        body_and_state=body_and_state,
    )


__all__ = [
    "EconomicEpochBodyAndStateV1",
    "CommitOutcomeStatusV1",
    "PublishedEconomicEpochV1",
    "CommitOutcomeV1",
    "GlobalEconomicCommitPortV1",
    "commit_verified_economic_epoch_v1",
]
