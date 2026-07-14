"""CBC tests for the governed lagged-checkpoint beacon adapter."""

from __future__ import annotations

import copy
import hashlib
import pickle

import pytest

from src.integration._zrpf_spot_v7_operational_capability_v2 import (
    _AUTHENTICATED_EXACT_CHECKPOINT_FINALITY_SEAL_V2,
    _AuthenticatedExactCheckpointFinalityTransitionV2,
)
from src.integration._zrpf_spot_v7_operational_gate import (
    _AuthenticatedCheckpointFinalityProjectionV2,
)
from src.integration.zrpf_spot_v7_lagged_checkpoint_beacon import (
    SpotV7LaggedCheckpointBeaconBindingErrorV1,
    _GovernedSpotV7LaggedCheckpointBeaconV1,
    bind_governed_spot_v7_lagged_checkpoint_beacon_v1,
    derive_lagged_checkpoint_beacon_commitment_v1,
)
from src.integration.zrpf_spot_v7_zeno_ledger_finality_adapter import (
    _AUTHENTICATED_CHECKPOINT_FINALITY_SEAL_V3,
    _AuthenticatedCheckpointFinalityProjectionV3,
    _AuthenticatedExactCheckpointFinalityTransitionV3,
)
from tests.integration.test_zrpf_spot_v7_operational_policy_v3 import (
    POLICY_ACTIVATION_EPOCH,
    _load,
    _manifest,
    _registry,
)


def _root(label: str) -> str:
    return "0x" + hashlib.sha256(label.encode("ascii")).hexdigest()


def _finality(
    policy_root: str,
    *,
    sequence: int = POLICY_ACTIVATION_EPOCH - 1,
    checkpoint_hash: str | None = None,
    evidence: bytes = b"finality-evidence-v1",
    application_id: str | None = None,
    chain_or_domain_id: str | None = None,
) -> _AuthenticatedExactCheckpointFinalityTransitionV2:
    projection = _AuthenticatedCheckpointFinalityProjectionV2(
        application_id=application_id or _root("application"),
        chain_or_domain_id=chain_or_domain_id or _root("domain"),
        epoch_id=sequence,
        proof_journal_hash=_root("proof-journal"),
        post_state_root=_root("post-state"),
        policy_root=policy_root,
        certificate_root=_root("certificate"),
        finality_evidence_root="0x" + hashlib.sha256(evidence).hexdigest(),
        prior_application_checkpoint_sequence=sequence - 1,
        prior_application_checkpoint_hash=_root("prior-checkpoint"),
        next_application_checkpoint_sequence=sequence,
        next_application_checkpoint_hash=(checkpoint_hash or _root("source-checkpoint")),
    )
    return _AuthenticatedExactCheckpointFinalityTransitionV2(
        projection,
        exact_certificate_bytes=b"certificate-v1",
        exact_finality_evidence_bytes=evidence,
        seal=_AUTHENTICATED_EXACT_CHECKPOINT_FINALITY_SEAL_V2,
    )


def _policy():
    registry = _registry()
    return _load(_manifest(registry), registry)


def _settlement_finality_v3() -> _AuthenticatedExactCheckpointFinalityTransitionV3:
    evidence = b"settlement-finality-v3-evidence"
    sequence = POLICY_ACTIVATION_EPOCH - 1
    return _AuthenticatedExactCheckpointFinalityTransitionV3(
        _AuthenticatedCheckpointFinalityProjectionV3(
            application_id=_root("application"),
            chain_or_domain_id=_root("domain"),
            epoch_id=sequence,
            proof_journal_hash=_root("proof-journal-v3"),
            post_state_root=_root("post-state-v3"),
            policy_root=_root("policy-v3"),
            certificate_root=_root("certificate-v3"),
            finality_evidence_root="0x" + hashlib.sha256(evidence).hexdigest(),
            prior_application_checkpoint_sequence=sequence - 1,
            prior_application_checkpoint_hash=_root("prior-checkpoint-v3"),
            next_application_checkpoint_sequence=sequence,
            next_application_checkpoint_hash=_root("source-checkpoint-v3"),
        ),
        exact_certificate_bytes=b"certificate-v3",
        exact_finality_evidence_bytes=evidence,
        seal=_AUTHENTICATED_CHECKPOINT_FINALITY_SEAL_V3,
    )


def test_lagged_finalized_checkpoint_derives_governed_beacon() -> None:
    policy = _policy()
    policy_root = policy._base_store_policy_for_governed_beacon_v1().checkpoint_finality_policy_root
    source = _finality(policy_root)

    governed = bind_governed_spot_v7_lagged_checkpoint_beacon_v1(
        operational_policy=policy,
        source_finality=source,
        checked_epoch=POLICY_ACTIVATION_EPOCH,
    )

    assert type(governed) is _GovernedSpotV7LaggedCheckpointBeaconV1
    beacon = governed._beacon_for_sampled_retrievability_v1()
    projection = governed._projection_for_governed_da_v2()
    assert beacon.beacon_epoch == POLICY_ACTIVATION_EPOCH
    assert projection.source_checkpoint_sequence == POLICY_ACTIVATION_EPOCH - 1
    assert projection.source_checkpoint_hash == _root("source-checkpoint")
    assert beacon.commitment == derive_lagged_checkpoint_beacon_commitment_v1(
        beacon_policy=policy._beacon_policy_for_governed_da_v2(),
        checked_epoch=POLICY_ACTIVATION_EPOCH,
        source_checkpoint_sequence=POLICY_ACTIVATION_EPOCH - 1,
        source_checkpoint_hash=_root("source-checkpoint"),
    )
    assert governed.governed_beacon_provenance_verified is True
    assert governed.beacon_unpredictability_verified is False
    assert governed.response_timing_provenance_verified is False
    assert governed.provider_independence_verified is False
    assert governed.continuous_availability_verified is False
    assert governed.public_future_availability_verified is False
    assert governed.release_authority is False
    assert governed.settlement_authority is False
    assert governed.production_authority is False


def test_beacon_commitment_excludes_quorum_evidence_and_certificate_roots() -> None:
    policy = _policy()
    policy_root = policy._base_store_policy_for_governed_beacon_v1().checkpoint_finality_policy_root
    first = bind_governed_spot_v7_lagged_checkpoint_beacon_v1(
        operational_policy=policy,
        source_finality=_finality(policy_root, evidence=b"quorum-a"),
        checked_epoch=POLICY_ACTIVATION_EPOCH,
    )
    second = bind_governed_spot_v7_lagged_checkpoint_beacon_v1(
        operational_policy=policy,
        source_finality=_finality(policy_root, evidence=b"quorum-b"),
        checked_epoch=POLICY_ACTIVATION_EPOCH,
    )

    assert (
        first._beacon_for_sampled_retrievability_v1().commitment
        == second._beacon_for_sampled_retrievability_v1().commitment
    )
    assert (
        first._projection_for_governed_da_v2().source_finality_evidence_root
        != second._projection_for_governed_da_v2().source_finality_evidence_root
    )


@pytest.mark.parametrize(
    ("sequence", "code"),
    (
        (POLICY_ACTIVATION_EPOCH, "SOURCE_CHECKPOINT_SEQUENCE"),
        (POLICY_ACTIVATION_EPOCH + 1, "SOURCE_CHECKPOINT_SEQUENCE"),
        (POLICY_ACTIVATION_EPOCH - 2, "SOURCE_CHECKPOINT_SEQUENCE"),
    ),
)
def test_same_current_future_or_wrong_lag_checkpoint_rejects(
    sequence: int,
    code: str,
) -> None:
    policy = _policy()
    policy_root = policy._base_store_policy_for_governed_beacon_v1().checkpoint_finality_policy_root

    with pytest.raises(SpotV7LaggedCheckpointBeaconBindingErrorV1) as captured:
        bind_governed_spot_v7_lagged_checkpoint_beacon_v1(
            operational_policy=policy,
            source_finality=_finality(policy_root, sequence=sequence),
            checked_epoch=POLICY_ACTIVATION_EPOCH,
        )

    assert captured.value.code == code


def test_settlement_finality_v3_is_not_accepted_as_lagged_beacon_source_v2() -> None:
    policy = _policy()

    with pytest.raises(TypeError, match="exact authenticated finality V2"):
        bind_governed_spot_v7_lagged_checkpoint_beacon_v1(
            operational_policy=policy,
            source_finality=_settlement_finality_v3(),
            checked_epoch=POLICY_ACTIVATION_EPOCH,
        )


@pytest.mark.parametrize(
    ("mutation", "code"),
    (
        ("application", "APPLICATION_MISMATCH"),
        ("domain", "DOMAIN_MISMATCH"),
        ("policy", "FINALITY_POLICY_ROOT_MISMATCH"),
        ("checkpoint", "SOURCE_CHECKPOINT_HASH_INVALID"),
    ),
)
def test_source_finality_binding_mutations_reject(mutation: str, code: str) -> None:
    policy = _policy()
    policy_root = policy._base_store_policy_for_governed_beacon_v1().checkpoint_finality_policy_root
    kwargs: dict[str, object] = {}
    if mutation == "application":
        kwargs["application_id"] = _root("wrong-app")
    elif mutation == "domain":
        kwargs["chain_or_domain_id"] = _root("wrong-domain")
    elif mutation == "policy":
        policy_root = _root("wrong-policy")

    source = _finality(policy_root, **kwargs)  # type: ignore[arg-type]
    if mutation == "checkpoint":
        object.__setattr__(
            source._projection,
            "next_application_checkpoint_hash",
            "0x" + "00" * 32,
        )
    with pytest.raises(SpotV7LaggedCheckpointBeaconBindingErrorV1) as captured:
        bind_governed_spot_v7_lagged_checkpoint_beacon_v1(
            operational_policy=policy,
            source_finality=source,
            checked_epoch=POLICY_ACTIVATION_EPOCH,
        )
    assert captured.value.code == code


def test_lagged_beacon_capability_is_nontransferable_and_rechecks_sources() -> None:
    policy = _policy()
    policy_root = policy._base_store_policy_for_governed_beacon_v1().checkpoint_finality_policy_root
    source = _finality(policy_root)
    governed = bind_governed_spot_v7_lagged_checkpoint_beacon_v1(
        operational_policy=policy,
        source_finality=source,
        checked_epoch=POLICY_ACTIVATION_EPOCH,
    )

    with pytest.raises(TypeError):
        copy.copy(governed)
    with pytest.raises(TypeError):
        copy.deepcopy(governed)
    with pytest.raises(TypeError):
        pickle.dumps(governed)
    with pytest.raises(TypeError):
        setattr(governed, "_seal", object())

    object.__setattr__(source._projection, "next_application_checkpoint_hash", _root("forged"))
    with pytest.raises(ValueError, match="projection drift"):
        governed._beacon_for_sampled_retrievability_v1()
