"""Bounded consecutive-epoch retrievability evidence for Spot V7.

This module joins a finite tuple of already-sealed Spot V7 DA prerequisites.
It proves that the same exact governed blob and certificate passed the complete
full-blob plus sampled-response boundary at every discrete epoch in one bounded
consecutive window.  It does not turn finitely many observations into a claim
of continuous availability, public retrievability, or future availability.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import NoReturn, SupportsIndex, final

from src.integration._zrpf_spot_v7_governed_da_projection_v2 import (
    _SpotV7GovernedDaPrerequisiteProjectionV2,
)
from src.integration.zeno_ledger_v0 import hash_v0
from src.integration.zrpf_sampled_retrievability_v1.model import (
    MAX_U64,
    require_root,
    require_token,
    require_u64,
)
from src.integration.zrpf_spot_v7_governed_da_prerequisite_v2 import (
    _GovernedSpotV7DataAvailabilityPrerequisiteV2,
)

__all__ = ()

MIN_LONGITUDINAL_RETRIEVABILITY_SAMPLES_V1 = 2
MAX_LONGITUDINAL_RETRIEVABILITY_SAMPLES_V1 = 8


class SpotV7LongitudinalRetrievabilityBindingErrorV1(ValueError):
    """Stable fail-closed rejection before a finite-window capability exists."""

    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(f"SPOT_V7_LONGITUDINAL_RETRIEVABILITY_REJECTED: {code}")


def _mismatch(code: str) -> NoReturn:
    raise SpotV7LongitudinalRetrievabilityBindingErrorV1(code)


def _require_bare_sha256(value: object, *, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise ValueError(f"{name} must be canonical lowercase SHA-256")
    return value


@dataclass(frozen=True, slots=True)
class _LongitudinalRetrievabilityObservationV1:
    """One authenticated epoch observation retained in canonical order."""

    checked_epoch: int
    source_checkpoint_sequence: int
    source_checkpoint_hash: str
    source_finality_policy_root: str
    source_finality_certificate_root: str
    source_finality_evidence_root: str
    beacon_commitment: str
    sampled_evidence_sha256: str
    accepted_provider_ids: tuple[str, ...]
    accepted_provider_set_root: str

    def __post_init__(self) -> None:
        require_u64(self.checked_epoch, name="longitudinal checked_epoch")
        require_u64(
            self.source_checkpoint_sequence,
            name="longitudinal source checkpoint sequence",
        )
        if self.source_checkpoint_sequence >= self.checked_epoch:
            raise ValueError("longitudinal source checkpoint must precede its sample")
        for name in (
            "source_checkpoint_hash",
            "source_finality_policy_root",
            "source_finality_certificate_root",
            "source_finality_evidence_root",
            "beacon_commitment",
            "accepted_provider_set_root",
        ):
            require_root(getattr(self, name), name=f"longitudinal {name}")
        _require_bare_sha256(
            self.sampled_evidence_sha256,
            name="longitudinal sampled evidence digest",
        )
        if type(self.accepted_provider_ids) is not tuple or not self.accepted_provider_ids:
            raise TypeError("longitudinal provider IDs must be a nonempty tuple")
        for provider_id in self.accepted_provider_ids:
            require_token(provider_id, name="longitudinal provider_id")
        if tuple(sorted(set(self.accepted_provider_ids))) != self.accepted_provider_ids:
            raise ValueError("longitudinal provider IDs must be canonical and distinct")

    def to_document(self) -> dict[str, object]:
        return {
            "accepted_provider_ids": list(self.accepted_provider_ids),
            "accepted_provider_set_root": self.accepted_provider_set_root,
            "beacon_commitment": self.beacon_commitment,
            "checked_epoch": self.checked_epoch,
            "sampled_evidence_sha256": self.sampled_evidence_sha256,
            "source_checkpoint_hash": self.source_checkpoint_hash,
            "source_checkpoint_sequence": self.source_checkpoint_sequence,
            "source_finality_certificate_root": self.source_finality_certificate_root,
            "source_finality_evidence_root": self.source_finality_evidence_root,
            "source_finality_policy_root": self.source_finality_policy_root,
        }


@dataclass(frozen=True, slots=True)
class _SpotV7LongitudinalRetrievabilityProjectionV1:
    """Finite-window projection over one exact governed content identity."""

    application_id: str
    chain_or_domain_id: str
    zeno_ledger_chain_id: str
    epoch_id: int
    start_checked_epoch: int
    end_checked_epoch: int
    sample_count: int
    certificate_root: str
    data_root: str
    chunk_root: str
    retention_through_epoch: int
    exact_blob_sha256: str
    full_blob_policy_root: str
    sampled_policy_root: str
    operational_policy_provenance_root: str
    operational_policy_manifest_sha256: str
    observations: tuple[_LongitudinalRetrievabilityObservationV1, ...]

    def __post_init__(self) -> None:
        if type(self.zeno_ledger_chain_id) is not str or not self.zeno_ledger_chain_id:
            raise ValueError("longitudinal ZenoLedger chain id must be nonempty")
        for name in (
            "application_id",
            "chain_or_domain_id",
            "certificate_root",
            "data_root",
            "chunk_root",
            "exact_blob_sha256",
            "full_blob_policy_root",
            "sampled_policy_root",
            "operational_policy_provenance_root",
        ):
            require_root(getattr(self, name), name=f"longitudinal {name}")
        for name in (
            "epoch_id",
            "start_checked_epoch",
            "end_checked_epoch",
            "retention_through_epoch",
        ):
            require_u64(getattr(self, name), name=f"longitudinal {name}")
        if type(self.sample_count) is not int or not (
            MIN_LONGITUDINAL_RETRIEVABILITY_SAMPLES_V1
            <= self.sample_count
            <= MAX_LONGITUDINAL_RETRIEVABILITY_SAMPLES_V1
        ):
            raise ValueError("longitudinal sample_count is outside the V1 bound")
        _require_bare_sha256(
            self.operational_policy_manifest_sha256,
            name="longitudinal operational policy manifest digest",
        )
        if type(self.observations) is not tuple or len(self.observations) != self.sample_count:
            raise TypeError("longitudinal observations must match sample_count")
        if any(
            type(observation) is not _LongitudinalRetrievabilityObservationV1
            for observation in self.observations
        ):
            raise TypeError("longitudinal observations have the wrong type")
        if self.observations[0].checked_epoch != self.start_checked_epoch or (
            self.observations[-1].checked_epoch != self.end_checked_epoch
        ):
            raise ValueError("longitudinal window endpoints disagree with observations")
        if self.retention_through_epoch < self.end_checked_epoch:
            raise ValueError("longitudinal window exceeds committed retention")

    @property
    def window_root(self) -> str:
        return hash_v0(
            "zrpf_spot_v7_bounded_longitudinal_retrievability_window_v1",
            self.to_document(),
        )

    def to_document(self) -> dict[str, object]:
        return {
            "application_id": self.application_id,
            "certificate_root": self.certificate_root,
            "chain_or_domain_id": self.chain_or_domain_id,
            "chunk_root": self.chunk_root,
            "data_root": self.data_root,
            "end_checked_epoch": self.end_checked_epoch,
            "epoch_id": self.epoch_id,
            "exact_blob_sha256": self.exact_blob_sha256,
            "full_blob_policy_root": self.full_blob_policy_root,
            "observations": [item.to_document() for item in self.observations],
            "operational_policy_manifest_sha256": (
                self.operational_policy_manifest_sha256
            ),
            "operational_policy_provenance_root": (
                self.operational_policy_provenance_root
            ),
            "retention_through_epoch": self.retention_through_epoch,
            "sample_count": self.sample_count,
            "sampled_policy_root": self.sampled_policy_root,
            "start_checked_epoch": self.start_checked_epoch,
            "zeno_ledger_chain_id": self.zeno_ledger_chain_id,
        }


class _GovernedSpotV7LongitudinalRetrievabilitySealV1:
    __slots__ = ()


_GOVERNED_SPOT_V7_LONGITUDINAL_RETRIEVABILITY_SEAL_V1 = (
    _GovernedSpotV7LongitudinalRetrievabilitySealV1()
)


@final
class _GovernedSpotV7LongitudinalRetrievabilityV1:
    """Non-transferable finite-window fact retaining every exact DA input."""

    __slots__ = ("_projection", "_samples", "_seal")

    _projection: _SpotV7LongitudinalRetrievabilityProjectionV1
    _samples: tuple[_GovernedSpotV7DataAvailabilityPrerequisiteV2, ...]
    _seal: _GovernedSpotV7LongitudinalRetrievabilitySealV1

    def __init__(
        self,
        projection: _SpotV7LongitudinalRetrievabilityProjectionV1,
        *,
        samples: tuple[_GovernedSpotV7DataAvailabilityPrerequisiteV2, ...],
        seal: _GovernedSpotV7LongitudinalRetrievabilitySealV1,
    ) -> None:
        if type(projection) is not _SpotV7LongitudinalRetrievabilityProjectionV1:
            raise TypeError("longitudinal projection has the wrong type")
        if seal is not _GOVERNED_SPOT_V7_LONGITUDINAL_RETRIEVABILITY_SEAL_V1:
            raise TypeError("longitudinal capability requires its module-private seal")
        exact_samples = _require_exact_samples(samples)
        expected = _derive_projection_v1(exact_samples)
        if projection != expected:
            raise ValueError("longitudinal retrievability projection drift")
        object.__setattr__(self, "_projection", projection)
        object.__setattr__(self, "_samples", exact_samples)
        object.__setattr__(self, "_seal", seal)

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("longitudinal retrievability capability cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("longitudinal retrievability capability cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("longitudinal retrievability capability cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("longitudinal retrievability capability cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("longitudinal retrievability capability cannot be serialized")

    def _has_private_seal(self) -> bool:
        return (
            getattr(self, "_seal", None)
            is _GOVERNED_SPOT_V7_LONGITUDINAL_RETRIEVABILITY_SEAL_V1
        )

    def _projection_for_longitudinal_downstream_binding_v1(
        self,
    ) -> _SpotV7LongitudinalRetrievabilityProjectionV1:
        if not self._has_private_seal():
            raise TypeError("longitudinal retrievability capability lacks its private seal")
        expected = _derive_projection_v1(self._samples)
        if expected != self._projection:
            raise ValueError("longitudinal retrievability projection drift")
        return self._projection

    @property
    def bounded_finite_window_retrievability_verified(self) -> bool:
        self._projection_for_longitudinal_downstream_binding_v1()
        return True

    @property
    def sampled_policy_governance_provenance_verified(self) -> bool:
        self._projection_for_longitudinal_downstream_binding_v1()
        return True

    @property
    def governed_beacon_provenance_verified(self) -> bool:
        self._projection_for_longitudinal_downstream_binding_v1()
        return True

    @property
    def current_operational_policy_release_head_verified(self) -> bool:
        return False

    @property
    def beacon_unpredictability_verified(self) -> bool:
        return False

    @property
    def response_timing_provenance_verified(self) -> bool:
        return False

    @property
    def provider_independence_verified(self) -> bool:
        return False

    @property
    def continuous_availability_verified(self) -> bool:
        return False

    @property
    def public_future_availability_verified(self) -> bool:
        return False

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


def _bind_bounded_spot_v7_longitudinal_retrievability_v1(
    samples: object,
) -> _GovernedSpotV7LongitudinalRetrievabilityV1:
    """Join a bounded consecutive tuple of exact governed DA capabilities."""

    exact_samples = _require_exact_samples(samples)
    projection = _derive_projection_v1(exact_samples)
    return _GovernedSpotV7LongitudinalRetrievabilityV1(
        projection,
        samples=exact_samples,
        seal=_GOVERNED_SPOT_V7_LONGITUDINAL_RETRIEVABILITY_SEAL_V1,
    )


def _require_exact_samples(
    value: object,
) -> tuple[_GovernedSpotV7DataAvailabilityPrerequisiteV2, ...]:
    if type(value) is not tuple:
        raise TypeError("longitudinal retrievability samples must be an exact tuple")
    samples = value
    if not (
        MIN_LONGITUDINAL_RETRIEVABILITY_SAMPLES_V1
        <= len(samples)
        <= MAX_LONGITUDINAL_RETRIEVABILITY_SAMPLES_V1
    ):
        _mismatch("SAMPLE_COUNT_OUT_OF_BOUNDS")
    for sample in samples:
        if type(sample) is not _GovernedSpotV7DataAvailabilityPrerequisiteV2:
            raise TypeError("longitudinal retrievability requires exact governed DA V2")
        if not sample._has_private_seal():
            raise TypeError("longitudinal retrievability requires sealed governed DA V2")
        sample._projection_for_downstream_binding_v2()
    return samples


def _content_identity(
    projection: _SpotV7GovernedDaPrerequisiteProjectionV2,
) -> tuple[object, ...]:
    value = projection
    return (
        value.base.application_id,
        value.base.chain_or_domain_id,
        value.zeno_ledger_chain_id,
        value.base.epoch_id,
        value.base.certificate_root,
        value.base.data_root,
        value.base.chunk_root,
        value.base.retention_through_epoch,
        value.base.exact_blob_sha256,
        value.base.full_blob_policy_root,
        value.base.sampled_policy_root,
        value.base.operational_policy_provenance_root,
        value.base.operational_policy_manifest_sha256,
    )


def _observation(
    projection: _SpotV7GovernedDaPrerequisiteProjectionV2,
) -> _LongitudinalRetrievabilityObservationV1:
    value = projection
    return _LongitudinalRetrievabilityObservationV1(
        checked_epoch=value.base.checked_epoch,
        source_checkpoint_sequence=value.source_checkpoint_sequence,
        source_checkpoint_hash=value.source_checkpoint_hash,
        source_finality_policy_root=value.source_finality_policy_root,
        source_finality_certificate_root=value.source_finality_certificate_root,
        source_finality_evidence_root=value.source_finality_evidence_root,
        beacon_commitment=value.base.beacon_commitment,
        sampled_evidence_sha256=value.base.sampled_evidence_sha256,
        accepted_provider_ids=value.base.accepted_provider_ids,
        accepted_provider_set_root=value.base.accepted_provider_set_root,
    )


def _derive_projection_v1(
    samples: tuple[_GovernedSpotV7DataAvailabilityPrerequisiteV2, ...],
) -> _SpotV7LongitudinalRetrievabilityProjectionV1:
    exact_samples = _require_exact_samples(samples)
    first = exact_samples[0]
    policy = first._policy
    first_projection = first._projection_for_downstream_binding_v2()
    identity = _content_identity(first_projection)
    observations: list[_LongitudinalRetrievabilityObservationV1] = []
    seen_checkpoint_hashes: set[str] = set()
    seen_beacons: set[str] = set()
    seen_evidence: set[str] = set()
    previous: _LongitudinalRetrievabilityObservationV1 | None = None
    for sample in exact_samples:
        if sample._policy is not policy:
            _mismatch("POLICY_CAPABILITY_MISMATCH")
        projection = sample._projection_for_downstream_binding_v2()
        if _content_identity(projection) != identity:
            _mismatch("CONTENT_IDENTITY_MISMATCH")
        observation = _observation(projection)
        if previous is not None:
            if previous.checked_epoch == MAX_U64 or (
                observation.checked_epoch != previous.checked_epoch + 1
            ):
                _mismatch("CHECKED_EPOCH_NOT_CONSECUTIVE")
            if previous.source_checkpoint_sequence == MAX_U64 or (
                observation.source_checkpoint_sequence
                != previous.source_checkpoint_sequence + 1
            ):
                _mismatch("SOURCE_CHECKPOINT_SEQUENCE_NOT_CONSECUTIVE")
        if observation.source_checkpoint_hash in seen_checkpoint_hashes:
            _mismatch("SOURCE_CHECKPOINT_REUSED")
        if observation.beacon_commitment in seen_beacons:
            _mismatch("BEACON_COMMITMENT_REUSED")
        if observation.sampled_evidence_sha256 in seen_evidence:
            _mismatch("SAMPLED_EVIDENCE_REUSED")
        seen_checkpoint_hashes.add(observation.source_checkpoint_hash)
        seen_beacons.add(observation.beacon_commitment)
        seen_evidence.add(observation.sampled_evidence_sha256)
        observations.append(observation)
        previous = observation
    base = first_projection.base
    return _SpotV7LongitudinalRetrievabilityProjectionV1(
        application_id=base.application_id,
        chain_or_domain_id=base.chain_or_domain_id,
        zeno_ledger_chain_id=first_projection.zeno_ledger_chain_id,
        epoch_id=base.epoch_id,
        start_checked_epoch=observations[0].checked_epoch,
        end_checked_epoch=observations[-1].checked_epoch,
        sample_count=len(observations),
        certificate_root=base.certificate_root,
        data_root=base.data_root,
        chunk_root=base.chunk_root,
        retention_through_epoch=base.retention_through_epoch,
        exact_blob_sha256=base.exact_blob_sha256,
        full_blob_policy_root=base.full_blob_policy_root,
        sampled_policy_root=base.sampled_policy_root,
        operational_policy_provenance_root=base.operational_policy_provenance_root,
        operational_policy_manifest_sha256=(base.operational_policy_manifest_sha256),
        observations=tuple(observations),
    )
