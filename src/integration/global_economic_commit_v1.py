"""Atomic in-memory conformance shell for verified economic epochs.

This adapter models one compare-and-swap publication capability.  It retains
state, the exact verified certificate, replay identity, receipt lineage, and
external outbox rows under one lock.  It does not provide durable storage,
crash recovery, consensus finality, or production writer authority.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from threading import Lock
from typing import Mapping

from ..core.global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from ..core.global_economic_proof_v1 import (
    VerifiedEconomicEpochV1,
    _snapshot_verified_economic_epoch_v1,
)
from ..core.global_economic_refinement_snapshot_v1 import (
    _require_exact_tuple_items,
    _snapshot_state_v1,
)
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
        if type(self.post_state) is not GlobalEconomicStateV1:
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


def _snapshot_body_and_state_v1(
    body: EconomicEpochBodyAndStateV1,
) -> EconomicEpochBodyAndStateV1:
    if type(body) is not EconomicEpochBodyAndStateV1:
        raise TypeError("commit body_and_state must have the exact typed value")
    for field_name in (
        "pre_state_root",
        "receipt_archive_root",
        "data_availability_root",
        "finality_root",
    ):
        if type(getattr(body, field_name)) is not str:
            raise TypeError(f"commit body {field_name} must be exact str")
    return EconomicEpochBodyAndStateV1(
        pre_state_root=body.pre_state_root,
        post_state=_snapshot_state_v1(body.post_state),
        ordered_command_body_hashes=tuple(
            _require_exact_tuple_items(
                body.ordered_command_body_hashes,
                str,
                "commit body command hashes",
            )
        ),
        receipt_archive_root=body.receipt_archive_root,
        data_availability_root=body.data_availability_root,
        finality_root=body.finality_root,
    )


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
    route_state_effect_refinement_roots: tuple[str, ...]
    route_state_projection_roots: tuple[str, ...]
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
        projection_roots = tuple(
            _require_exact_tuple_items(
                self.route_state_projection_roots,
                str,
                "published epoch route state projection roots",
            )
        )
        if not 1 <= len(projection_roots) <= MAX_EPOCH_COMMANDS_V1:
            raise ValueError(
                "published epoch requires between one and 64 route state projection roots"
            )
        if len(projection_roots) != len(set(projection_roots)):
            raise ValueError("published epoch route state projection roots must be unique")
        for index, root in enumerate(projection_roots):
            _require_root(root, name=f"published epoch route state projection root[{index}]")
        refinement_roots = tuple(
            _require_exact_tuple_items(
                self.route_state_effect_refinement_roots,
                str,
                "published epoch route state/effect refinement roots",
            )
        )
        if len(refinement_roots) != len(projection_roots):
            raise ValueError(
                "published epoch route state/effect refinement count mismatch"
            )
        if len(refinement_roots) != len(set(refinement_roots)):
            raise ValueError(
                "published epoch route state/effect refinement roots must be unique"
            )
        for index, root in enumerate(refinement_roots):
            _require_root(
                root,
                name=f"published epoch route state/effect refinement root[{index}]",
            )
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
            "route_state_effect_refinement_roots": (
                self.route_state_effect_refinement_roots
            ),
            "route_state_projection_roots": self.route_state_projection_roots,
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
        if type(profile) is not EconomicProfileSnapshotV1:
            raise TypeError("commit port profile must have the exact typed value")
        if type(initial_state) is not GlobalEconomicStateV1:
            raise TypeError("commit port initial state must have the exact typed value")
        owned_profile = snapshot_economic_profile_v1(profile)
        if owned_profile.status is not ProfileStatusV1.ACTIVE:
            raise ValueError("commit port requires an ACTIVE economic profile")
        owned_initial_state = _snapshot_state_v1(initial_state)
        validate_global_state_profile_v1(owned_initial_state, owned_profile)
        self._profile = owned_profile
        self._state = owned_initial_state
        self._records: dict[str, PublishedEconomicEpochV1] = {}
        self._lock = Lock()

    @property
    def profile(self) -> EconomicProfileSnapshotV1:
        return snapshot_economic_profile_v1(self._profile)

    @property
    def state(self) -> GlobalEconomicStateV1:
        with self._lock:
            return _snapshot_state_v1(self._state)

    @property
    def records(self) -> tuple[PublishedEconomicEpochV1, ...]:
        with self._lock:
            return tuple(replace(self._records[key]) for key in sorted(self._records))

    def commit_verified_economic_epoch(
        self,
        *,
        expected_head: str,
        expected_profile: str,
        verified_epoch: VerifiedEconomicEpochV1,
        body_and_state: EconomicEpochBodyAndStateV1,
    ) -> CommitOutcomeV1:
        """Atomically publish the exact verified epoch tuple or a typed no-op."""

        if type(expected_head) is not str:
            raise TypeError("commit expected head must be exact str")
        if type(expected_profile) is not str:
            raise TypeError("commit expected profile must be exact str")
        _require_root(expected_head, name="commit expected head")
        _require_root(expected_profile, name="commit expected profile")
        if type(verified_epoch) is not VerifiedEconomicEpochV1:
            raise TypeError("commit requires VerifiedEconomicEpochV1")
        owned_verified_epoch = _snapshot_verified_economic_epoch_v1(verified_epoch)
        if type(body_and_state) is not EconomicEpochBodyAndStateV1:
            raise TypeError("commit body_and_state is invalid")
        owned_body = _snapshot_body_and_state_v1(body_and_state)
        with self._lock:
            return self._commit_locked(
                expected_head=expected_head,
                expected_profile=expected_profile,
                verified_epoch=owned_verified_epoch,
                body_and_state=owned_body,
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
        try:
            active_profile = snapshot_economic_profile_v1(self._profile)
        except (TypeError, ValueError):
            return self._reject(
                CommitOutcomeStatusV1.BINDING_REJECTED,
                commit_id,
                "active profile content binding is invalid",
            )
        if active_profile.status is not ProfileStatusV1.ACTIVE:
            return self._reject(
                CommitOutcomeStatusV1.PROFILE_MISMATCH,
                commit_id,
                "active profile status is invalid",
            )
        self._profile = active_profile
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
                _snapshot_state_v1(self._state),
                commit_id,
                record=replace(previous),
            )
        if expected_head != self._state.state_root:
            return self._reject(CommitOutcomeStatusV1.STALE_HEAD, commit_id, "expected head is stale")
        reason = self._binding_rejection_reason(verified_epoch, body_and_state)
        if reason is not None:
            return self._reject(CommitOutcomeStatusV1.BINDING_REJECTED, commit_id, reason)
        certificate = verified_epoch.certificate
        record = PublishedEconomicEpochV1(
            commit_id=commit_id,
            certificate_root=verified_epoch.verified_certificate_root,
            profile_root=certificate.profile_root,
            writer_epoch=certificate.writer_epoch,
            pre_state_root=certificate.pre_state_root,
            post_state_root=certificate.post_state_root,
            body_commitment=certificate.body_commitment,
            data_availability_root=certificate.data_availability_root,
            finality_root=certificate.finality_root,
            receipt_root=certificate.receipt_root,
            receipt_archive_root=body_and_state.receipt_archive_root,
            effect_plan_root=verified_epoch.verified_effect_plan_root,
            route_state_effect_refinement_roots=(
                verified_epoch.route_state_effect_refinement_roots
            ),
            route_state_projection_roots=verified_epoch.route_state_projection_roots,
            release_observation_root=hash_global_v1(
                "global-economic-release-observation-v1",
                {
                    "profile_root": self._profile.profile_id,
                    "lane_registry_root": self._profile.lane_registry.registry_root,
                    "route_registry_root": self._profile.route_registry.registry_root,
                },
            ),
        )
        self._state = _snapshot_state_v1(body_and_state.post_state)
        self._records[commit_id] = record
        return CommitOutcomeV1(
            CommitOutcomeStatusV1.COMMITTED,
            _snapshot_state_v1(self._state),
            commit_id,
            record=replace(record),
        )

    def _binding_rejection_reason(
        self,
        verified_epoch: VerifiedEconomicEpochV1,
        body_and_state: EconomicEpochBodyAndStateV1,
    ) -> str | None:
        certificate = verified_epoch.certificate
        retained_refinement = verified_epoch.state_effect_refinement
        post_state = body_and_state.post_state
        try:
            validate_global_state_profile_v1(post_state, self._profile)
        except ValueError as exc:
            return str(exc)
        try:
            (
                route_state_projection_roots,
                route_state_effect_refinement_roots,
            ) = verified_epoch.recheck_route_state_evidence(
                pre_state=self._state,
                post_state=post_state,
            )
        except (TypeError, ValueError) as exc:
            return f"route state projection recheck rejected: {exc}"
        if route_state_projection_roots != verified_epoch.route_state_projection_roots:
            return "route state projection root mismatch"
        if (
            route_state_effect_refinement_roots
            != verified_epoch.route_state_effect_refinement_roots
        ):
            return "route state/effect refinement root mismatch"
        try:
            refinement = verified_epoch.recheck_state_effect_refinement(
                pre_state=self._state,
                post_state=post_state,
            )
        except (TypeError, ValueError) as exc:
            return f"state/effect refinement recheck rejected: {exc}"
        bindings = (
            (
                certificate.certificate_root,
                verified_epoch.verified_certificate_root,
                "verified certificate root",
            ),
            (
                verified_epoch.effect_plan.effect_plan_root,
                verified_epoch.verified_effect_plan_root,
                "verified effect plan root",
            ),
            (
                retained_refinement.refinement_root,
                verified_epoch.verified_state_effect_refinement_root,
                "verified retained refinement root",
            ),
            (
                refinement.refinement_root,
                verified_epoch.verified_state_effect_refinement_root,
                "rechecked refinement root",
            ),
            (certificate.chain_id, self._state.chain_id, "certificate chain"),
            (certificate.deployment_root, self._state.deployment_root, "certificate deployment"),
            (certificate.profile_root, self._profile.profile_id, "certificate profile"),
            (certificate.writer_epoch, self._profile.authority_epoch, "writer epoch"),
            (certificate.pre_state_root, self._state.state_root, "pre-state root"),
            (body_and_state.pre_state_root, self._state.state_root, "body pre-state root"),
            (certificate.post_state_root, post_state.state_root, "post-state root"),
            (
                refinement.pre_state_root,
                self._state.state_root,
                "state refinement pre-state root",
            ),
            (
                refinement.post_state_root,
                post_state.state_root,
                "state refinement post-state root",
            ),
            (
                refinement.effect_plan_root,
                verified_epoch.effect_plan.effect_plan_root,
                "state refinement effect plan root",
            ),
            (
                retained_refinement.pre_state_root,
                refinement.pre_state_root,
                "retained refinement pre-state root",
            ),
            (
                retained_refinement.post_state_root,
                refinement.post_state_root,
                "retained refinement post-state root",
            ),
            (
                retained_refinement.effect_plan_root,
                refinement.effect_plan_root,
                "retained refinement effect plan root",
            ),
            (
                certificate.pre_state_root,
                refinement.pre_state_root,
                "certificate refinement pre-state root",
            ),
            (
                certificate.post_state_root,
                refinement.post_state_root,
                "certificate refinement post-state root",
            ),
            (
                certificate.effect_plan_root,
                refinement.effect_plan_root,
                "certificate refinement effect plan root",
            ),
            (
                verified_epoch.receipt_digest,
                certificate.receipt_root,
                "verified receipt root",
            ),
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
        refinement = verified_epoch.state_effect_refinement
        try:
            validate_global_state_profile_v1(body_and_state.post_state, self._profile)
        except ValueError as exc:
            return str(exc)
        bindings = (
            (
                certificate.certificate_root,
                verified_epoch.verified_certificate_root,
                "verified certificate root",
            ),
            (
                verified_epoch.effect_plan.effect_plan_root,
                verified_epoch.verified_effect_plan_root,
                "verified effect plan root",
            ),
            (
                refinement.refinement_root,
                verified_epoch.verified_state_effect_refinement_root,
                "verified retained refinement root",
            ),
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
            (
                verified_epoch.route_state_projection_roots,
                previous.route_state_projection_roots,
                "route state projection roots",
            ),
            (
                verified_epoch.route_state_effect_refinement_roots,
                previous.route_state_effect_refinement_roots,
                "route state/effect refinement roots",
            ),
            (refinement.pre_state_root, previous.pre_state_root, "state refinement pre-state root"),
            (refinement.post_state_root, previous.post_state_root, "state refinement post-state root"),
            (refinement.effect_plan_root, previous.effect_plan_root, "state refinement effect plan root"),
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
        return CommitOutcomeV1(
            status,
            _snapshot_state_v1(self._state),
            commit_id,
            reason=reason,
        )


def commit_verified_economic_epoch_v1(
    port: GlobalEconomicCommitPortV1,
    *,
    expected_head: str,
    expected_profile: str,
    verified_epoch: VerifiedEconomicEpochV1,
    body_and_state: EconomicEpochBodyAndStateV1,
) -> CommitOutcomeV1:
    """Functional facade matching the GlobalSettlementABI publication name."""

    if type(port) is not GlobalEconomicCommitPortV1:
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
