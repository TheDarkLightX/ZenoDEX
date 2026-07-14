"""Governed Spot V7 beacon derived from an exact prior finalized checkpoint.

The adapter consumes a signed V3 operational policy and an already sealed
checkpoint-finality V2 capability.  It requires the finalized checkpoint
sequence to equal ``checked_epoch - source_epoch_lag``.  Current, future, and
arbitrarily older checkpoints reject.  The challenge commitment deliberately
excludes finality certificate and quorum-evidence roots so distinct valid quorum
subsets for the same finalized checkpoint derive one challenge beacon.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import NoReturn, SupportsIndex, cast, final

from src.integration._zrpf_spot_v7_operational_capability_v2 import (
    _AuthenticatedExactCheckpointFinalityTransitionV2,
)
from src.integration._zrpf_spot_v7_operational_policy_v3 import (
    BeaconPolicyV1,
    _GovernedSpotV7OperationalPolicyV3,
    _require_governed_operational_policy_v3,
)
from src.integration.zeno_ledger_v0 import hash_v0
from src.integration.zrpf_sampled_retrievability_v1.model import (
    BeaconCommitmentV1,
    require_root,
    require_u64,
)


class SpotV7LaggedCheckpointBeaconBindingErrorV1(ValueError):
    """Stable fail-closed rejection at the governed beacon boundary."""

    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(f"SPOT_V7_LAGGED_CHECKPOINT_BEACON_REJECTED: {code}")


def _mismatch(code: str) -> NoReturn:
    raise SpotV7LaggedCheckpointBeaconBindingErrorV1(code)


@dataclass(frozen=True, slots=True)
class _GovernedSpotV7LaggedCheckpointBeaconProjectionV1:
    application_id: str
    chain_or_domain_id: str
    zeno_ledger_chain_id: str
    checked_epoch: int
    beacon_source_id: str
    beacon_policy_root: str
    source_network_id: str
    source_protocol_id: str
    source_epoch_lag: int
    source_checkpoint_sequence: int
    source_checkpoint_hash: str
    source_finality_policy_root: str
    source_finality_certificate_root: str
    source_finality_evidence_root: str
    beacon_commitment: str

    def __post_init__(self) -> None:
        if type(self.zeno_ledger_chain_id) is not str or not self.zeno_ledger_chain_id:
            raise ValueError("governed beacon chain id must be nonempty")
        for name in ("checked_epoch", "source_epoch_lag", "source_checkpoint_sequence"):
            require_u64(getattr(self, name), name=f"governed beacon {name}")
        for name in (
            "application_id",
            "chain_or_domain_id",
            "beacon_source_id",
            "beacon_policy_root",
            "source_network_id",
            "source_protocol_id",
            "source_checkpoint_hash",
            "source_finality_policy_root",
            "source_finality_certificate_root",
            "source_finality_evidence_root",
            "beacon_commitment",
        ):
            require_root(getattr(self, name), name=f"governed beacon {name}")


class _GovernedLaggedCheckpointBeaconSealV1:
    __slots__ = ()


_GOVERNED_LAGGED_CHECKPOINT_BEACON_SEAL_V1 = _GovernedLaggedCheckpointBeaconSealV1()


@final
class _GovernedSpotV7LaggedCheckpointBeaconV1:
    """Non-transferable governed checkpoint beacon; no availability authority."""

    __slots__ = ("_policy", "_projection", "_source_finality", "_seal")

    _policy: _GovernedSpotV7OperationalPolicyV3
    _projection: _GovernedSpotV7LaggedCheckpointBeaconProjectionV1
    _source_finality: _AuthenticatedExactCheckpointFinalityTransitionV2
    _seal: _GovernedLaggedCheckpointBeaconSealV1

    def __init__(
        self,
        projection: _GovernedSpotV7LaggedCheckpointBeaconProjectionV1,
        *,
        operational_policy: _GovernedSpotV7OperationalPolicyV3,
        source_finality: _AuthenticatedExactCheckpointFinalityTransitionV2,
        seal: _GovernedLaggedCheckpointBeaconSealV1,
    ) -> None:
        if type(projection) is not _GovernedSpotV7LaggedCheckpointBeaconProjectionV1:
            raise TypeError("governed beacon projection has the wrong type")
        if seal is not _GOVERNED_LAGGED_CHECKPOINT_BEACON_SEAL_V1:
            raise TypeError("governed beacon requires the module-private seal")
        expected = _derive_projection_v1(
            operational_policy=operational_policy,
            source_finality=source_finality,
            checked_epoch=projection.checked_epoch,
        )
        if projection != expected:
            raise ValueError("governed lagged checkpoint beacon projection drift")
        object.__setattr__(self, "_policy", operational_policy)
        object.__setattr__(self, "_source_finality", source_finality)
        object.__setattr__(self, "_projection", projection)
        object.__setattr__(self, "_seal", seal)

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("governed lagged checkpoint beacon cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("governed lagged checkpoint beacon cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("governed lagged checkpoint beacon cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("governed lagged checkpoint beacon cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("governed lagged checkpoint beacon cannot be serialized")

    def _has_private_seal(self) -> bool:
        return (
            getattr(self, "_seal", None) is _GOVERNED_LAGGED_CHECKPOINT_BEACON_SEAL_V1
        )

    def _projection_for_governed_da_v2(
        self,
    ) -> _GovernedSpotV7LaggedCheckpointBeaconProjectionV1:
        if not self._has_private_seal():
            raise TypeError("governed lagged checkpoint beacon lacks its private seal")
        expected = _derive_projection_v1(
            operational_policy=self._policy,
            source_finality=self._source_finality,
            checked_epoch=self._projection.checked_epoch,
        )
        if expected != self._projection:
            raise ValueError("governed lagged checkpoint beacon projection drift")
        return self._projection

    def _beacon_for_sampled_retrievability_v1(self) -> BeaconCommitmentV1:
        projection = self._projection_for_governed_da_v2()
        return BeaconCommitmentV1.validated(
            source_id=projection.beacon_source_id,
            policy_hash=projection.beacon_policy_root,
            beacon_epoch=projection.checked_epoch,
            commitment=projection.beacon_commitment,
        )

    @property
    def governed_beacon_provenance_verified(self) -> bool:
        self._projection_for_governed_da_v2()
        return True

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


def derive_lagged_checkpoint_beacon_commitment_v1(
    *,
    beacon_policy: BeaconPolicyV1,
    checked_epoch: int,
    source_checkpoint_sequence: int,
    source_checkpoint_hash: str,
) -> str:
    """Derive a challenge commitment without quorum-subset evidence roots."""

    if type(beacon_policy) is not BeaconPolicyV1:
        raise TypeError("beacon commitment requires exact BeaconPolicyV1")
    checked = require_u64(checked_epoch, name="beacon checked_epoch")
    source_sequence = require_u64(
        source_checkpoint_sequence,
        name="beacon source checkpoint sequence",
    )
    source_hash = require_root(
        source_checkpoint_hash,
        name="beacon source checkpoint hash",
    )
    return hash_v0(
        "zrpf_spot_v7_lagged_checkpoint_beacon_commitment_v1",
        {
            "beacon_policy_root": beacon_policy.policy_root,
            "checked_epoch": checked,
            "source_checkpoint_hash": source_hash,
            "source_checkpoint_sequence": source_sequence,
            "source_epoch_lag": beacon_policy.source_epoch_lag,
            "source_id": beacon_policy.source_id,
            "source_network_id": beacon_policy.source_network_id,
            "source_protocol_id": beacon_policy.source_protocol_id,
        },
    )


def bind_governed_spot_v7_lagged_checkpoint_beacon_v1(
    *,
    operational_policy: object,
    source_finality: object,
    checked_epoch: int,
) -> _GovernedSpotV7LaggedCheckpointBeaconV1:
    """Bind one exact prior finalized checkpoint to the signed beacon policy."""

    policy = _require_governed_operational_policy_v3(operational_policy)
    source = _require_authenticated_finality_v2(source_finality)
    checked = require_u64(checked_epoch, name="governed beacon checked_epoch")
    try:
        policy._require_active_at_epoch_for_governed_da_v2(checked)
    except ValueError as exc:
        raise SpotV7LaggedCheckpointBeaconBindingErrorV1("POLICY_INACTIVE") from exc
    projection = _derive_projection_v1(
        operational_policy=policy,
        source_finality=source,
        checked_epoch=checked,
    )
    return _GovernedSpotV7LaggedCheckpointBeaconV1(
        projection,
        operational_policy=policy,
        source_finality=source,
        seal=_GOVERNED_LAGGED_CHECKPOINT_BEACON_SEAL_V1,
    )


def _require_authenticated_finality_v2(
    value: object,
) -> _AuthenticatedExactCheckpointFinalityTransitionV2:
    if type(value) is not _AuthenticatedExactCheckpointFinalityTransitionV2:
        raise TypeError("governed beacon requires exact authenticated finality V2")
    authenticated = cast(_AuthenticatedExactCheckpointFinalityTransitionV2, value)
    if not authenticated._has_private_seal():
        raise TypeError("governed beacon requires sealed authenticated finality V2")
    projection = authenticated._projection
    if (
        "0x" + hashlib.sha256(authenticated._exact_finality_evidence_bytes).hexdigest()
        != projection.finality_evidence_root
    ):
        raise ValueError("authenticated finality evidence drift")
    return authenticated


def _derive_projection_v1(
    *,
    operational_policy: _GovernedSpotV7OperationalPolicyV3,
    source_finality: _AuthenticatedExactCheckpointFinalityTransitionV2,
    checked_epoch: int,
) -> _GovernedSpotV7LaggedCheckpointBeaconProjectionV1:
    policy = _require_governed_operational_policy_v3(operational_policy)
    source = _require_authenticated_finality_v2(source_finality)
    checked = require_u64(checked_epoch, name="governed beacon checked_epoch")
    policy_projection = policy._projection_for_governed_da_v2()
    base = policy._base_store_policy_for_governed_beacon_v1()
    beacon = policy._beacon_policy_for_governed_da_v2()
    finality = source._projection
    if checked < beacon.source_epoch_lag:
        _mismatch("SOURCE_CHECKPOINT_SEQUENCE")
    expected_sequence = checked - beacon.source_epoch_lag
    checks = (
        (finality.application_id == policy_projection.application_id, "APPLICATION_MISMATCH"),
        (
            finality.chain_or_domain_id == policy_projection.chain_or_domain_id,
            "DOMAIN_MISMATCH",
        ),
        (
            finality.policy_root == base.checkpoint_finality_policy_root,
            "FINALITY_POLICY_ROOT_MISMATCH",
        ),
        (
            finality.next_application_checkpoint_sequence == expected_sequence,
            "SOURCE_CHECKPOINT_SEQUENCE",
        ),
        (finality.epoch_id == expected_sequence, "SOURCE_CHECKPOINT_EPOCH"),
    )
    for accepted, code in checks:
        if not accepted:
            _mismatch(code)
    try:
        source_hash = require_root(
            finality.next_application_checkpoint_hash,
            name="source checkpoint hash",
        )
    except (TypeError, ValueError) as exc:
        raise SpotV7LaggedCheckpointBeaconBindingErrorV1(
            "SOURCE_CHECKPOINT_HASH_INVALID"
        ) from exc
    commitment = derive_lagged_checkpoint_beacon_commitment_v1(
        beacon_policy=beacon,
        checked_epoch=checked,
        source_checkpoint_sequence=expected_sequence,
        source_checkpoint_hash=source_hash,
    )
    return _GovernedSpotV7LaggedCheckpointBeaconProjectionV1(
        application_id=policy_projection.application_id,
        chain_or_domain_id=policy_projection.chain_or_domain_id,
        zeno_ledger_chain_id=policy_projection.zeno_ledger_chain_id,
        checked_epoch=checked,
        beacon_source_id=beacon.source_id,
        beacon_policy_root=beacon.policy_root,
        source_network_id=beacon.source_network_id,
        source_protocol_id=beacon.source_protocol_id,
        source_epoch_lag=beacon.source_epoch_lag,
        source_checkpoint_sequence=expected_sequence,
        source_checkpoint_hash=source_hash,
        source_finality_policy_root=finality.policy_root,
        source_finality_certificate_root=finality.certificate_root,
        source_finality_evidence_root=finality.finality_evidence_root,
        beacon_commitment=commitment,
    )


def _require_governed_lagged_checkpoint_beacon_v1(
    value: object,
) -> _GovernedSpotV7LaggedCheckpointBeaconV1:
    if type(value) is not _GovernedSpotV7LaggedCheckpointBeaconV1:
        raise TypeError("governed DA requires exact lagged checkpoint beacon V1")
    if not value._has_private_seal():
        raise TypeError("governed DA requires sealed lagged checkpoint beacon V1")
    value._projection_for_governed_da_v2()
    return value
