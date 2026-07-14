"""CBC tests for the authority-neutral Spot V7 V3 operational join."""

from __future__ import annotations

import copy
import hashlib
import pickle
from collections.abc import Callable
from dataclasses import replace
from unittest.mock import patch

import pytest

import src.integration.zrpf_spot_v7_governed_da_prerequisite_v2 as da_module
import tests.integration.test_zrpf_spot_v7_governed_da_prerequisite_v2 as da_test
import tests.integration.test_zrpf_spot_v7_operational_policy_v3 as policy_test
import tests.integration.test_zrpf_spot_v7_settlement_envelope_replay as replay_test
from src.integration._zrpf_spot_v7_operational_capability_v3 import (
    SpotV7OperationalCapabilityBindingErrorV3,
    _bind_spot_v7_operational_commit_capability_v3,
    _SpotV7AtomicEconomicCommitCapabilityV3,
)
from src.integration._zrpf_spot_v7_operational_mechanics import (
    _encode_checkpoint_finality_certificate_v2,
    _finality_certificate_root_v2,
)
from src.integration._zrpf_spot_v7_settlement_durable_replay import (
    _reverify_persisted_spot_v7_settlement_replay_v2,
)
from src.integration._zrpf_spot_v7_zeno_ledger_finality_contract import _ZERO_ROOT
from src.integration.dex_engine import DexEngineConfig
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.zeno_ledger_replay import replay_engine_config_document_v0
from src.integration.zeno_ledger_v0 import canonical_header_hash_v0, canonical_json_bytes_v0
from src.integration.zrpf_spot_v7_zeno_ledger_finality_adapter import (
    _AUTHENTICATED_CHECKPOINT_FINALITY_SEAL_V3,
    _AuthenticatedCheckpointFinalityProjectionV3,
    _AuthenticatedExactCheckpointFinalityTransitionV3,
)


def _valid_prerequisites() -> tuple[object, object, object, object, object, bytes]:
    epoch = policy_test.POLICY_ACTIVATION_EPOCH
    with (
        patch.object(policy_test, "CHAIN_ID", replay_test._CHAIN_ID),
        patch.object(da_test, "EPOCH_ID", epoch),
        patch.object(da_test, "RETENTION_THROUGH_EPOCH", epoch + 15),
    ):
        policy, _beacon, _sampled, governed_sample, full_blob = da_test._valid()
        data_availability = da_module._bind_governed_spot_v7_da_prerequisite_v2(
            operational_policy=policy,
            exact_full_blob=full_blob,
            governed_sampled_response=governed_sample,
        )

    da_projection = data_availability._projection_for_downstream_binding_v2()
    policy_projection = policy._projection_for_governed_da_v2()
    partial = replace(
        replay_test._candidate(),
        application_id=policy_projection.application_id,
        chain_or_domain_id=policy_projection.chain_or_domain_id,
        epoch_id=epoch,
        data_availability_certificate_root=da_projection.base.certificate_root,
        data_root=da_projection.base.data_root,
        exact_v7_journal_bytes=b"placeholder",
    )
    candidate = replace(
        partial,
        exact_v7_journal_bytes=replay_test._v7_journal(partial),
    )
    settlement = replay_test._settlement(candidate)
    config = replay_engine_config_document_v0(
        DexEngineConfig(chain_id=replay_test._CHAIN_ID)
    )
    envelope = replay_test.build_spot_v7_settlement_envelope_v1(settlement)
    body = replay_test._body(candidate, envelope)
    parent_candidate = replace(
        candidate,
        epoch_id=epoch - 1,
        post_state_root=candidate.pre_state_root,
    )
    parent_header = replay_test._header(parent_candidate, body, config)
    header = replay_test._header(candidate, body, config)
    header["prev_header_hash"] = canonical_header_hash_v0(parent_header)
    pre_state, _post_state = replay_test._states()
    observation = replay_test.SpotV7SettlementEnvelopeReplayAdapterV2(
        config
    ).authenticate(
        settlement=settlement,
        header=header,
        body=body,
        pre_snapshot=snapshot_from_state(pre_state).data,
        parent_header=parent_header,
    )
    persisted = (
        observation._durable_replay_packet_for_history_reverification()
        ._persisted_inputs_for_storage()
    )
    durable_replay = _reverify_persisted_spot_v7_settlement_replay_v2(
        settlement=settlement,
        persisted=persisted,
        exact_parent_header_bytes=canonical_json_bytes_v0(parent_header),
    )
    finality = _finality(policy, candidate, observation)
    return (
        settlement,
        policy,
        data_availability,
        finality,
        durable_replay,
        canonical_json_bytes_v0(parent_header),
    )


def _finality(policy: object, candidate: object, observation: object) -> object:
    store_policy = policy._base_store_policy_for_finality_v3()  # type: ignore[attr-defined]
    replay_projection = observation._projection_for_finality_adapter()  # type: ignore[attr-defined]
    evidence = b'{"schema":"test-only-finality-v3-evidence"}'
    evidence_root = "0x" + hashlib.sha256(evidence).hexdigest()
    journal_hash = "0x" + hashlib.sha256(
        candidate.exact_v7_journal_bytes  # type: ignore[attr-defined]
    ).hexdigest()
    parent_hash = replay_projection.parent_header_hash or _ZERO_ROOT
    certificate_root = _finality_certificate_root_v2(
        policy=store_policy,
        epoch_id=candidate.epoch_id,  # type: ignore[attr-defined]
        proof_journal_hash=journal_hash,
        post_state_root=candidate.post_state_root,  # type: ignore[attr-defined]
        sequence=1,
        checkpoint_hash=replay_projection.header_hash,
        parent_hash=parent_hash,
        evidence_root=evidence_root,
        policy_root=store_policy.checkpoint_finality_policy_root,
    )
    certificate = _encode_checkpoint_finality_certificate_v2(
        policy=store_policy,
        epoch_id=candidate.epoch_id,  # type: ignore[attr-defined]
        proof_journal_hash=journal_hash,
        post_state_root=candidate.post_state_root,  # type: ignore[attr-defined]
        sequence=1,
        checkpoint_hash=replay_projection.header_hash,
        parent_hash=parent_hash,
        evidence_root=evidence_root,
        policy_root=store_policy.checkpoint_finality_policy_root,
        certificate_root=certificate_root,
    )
    projection = _AuthenticatedCheckpointFinalityProjectionV3(
        application_id=candidate.application_id,  # type: ignore[attr-defined]
        chain_or_domain_id=candidate.chain_or_domain_id,  # type: ignore[attr-defined]
        epoch_id=candidate.epoch_id,  # type: ignore[attr-defined]
        proof_journal_hash=journal_hash,
        post_state_root=candidate.post_state_root,  # type: ignore[attr-defined]
        policy_root=store_policy.checkpoint_finality_policy_root,
        certificate_root=certificate_root,
        finality_evidence_root=evidence_root,
        prior_application_checkpoint_sequence=0,
        prior_application_checkpoint_hash=parent_hash,
        next_application_checkpoint_sequence=1,
        next_application_checkpoint_hash=replay_projection.header_hash,
    )
    return _AuthenticatedExactCheckpointFinalityTransitionV3(
        projection,
        exact_certificate_bytes=certificate,
        exact_finality_evidence_bytes=evidence,
        seal=_AUTHENTICATED_CHECKPOINT_FINALITY_SEAL_V3,
    )


def test_v3_join_recomposes_all_exact_prerequisites_and_preserves_nonclaims() -> None:
    settlement, policy, data_availability, finality, durable_replay, parent = (
        _valid_prerequisites()
    )

    capability = _bind_spot_v7_operational_commit_capability_v3(
        settlement=settlement,
        policy=policy,
        data_availability=data_availability,
        finality=finality,
        durable_replay=durable_replay,
        exact_parent_header_bytes=parent,
    )

    assert type(capability) is _SpotV7AtomicEconomicCommitCapabilityV3
    packet = capability._packet_for_atomic_store_v4()
    assert packet.candidate.epoch_id == policy_test.POLICY_ACTIVATION_EPOCH
    assert packet.data_availability.base.data_root == packet.candidate.data_root
    assert packet.finality.next_application_checkpoint_hash == (
        packet.durable_replay_packet._projection_for_history_reverification().header_hash
    )
    assert capability.durable_settlement_replay_reverified is True
    assert capability.sampled_policy_governance_provenance_verified is True
    assert capability.governed_beacon_provenance_verified is True
    assert capability.public_future_availability_verified is False
    assert capability.release_authority is False
    assert capability.settlement_authority is False
    assert capability.production_authority is False


@pytest.mark.parametrize(
    "field",
    (
        "settlement",
        "policy",
        "data_availability",
        "finality",
        "durable_replay",
    ),
)
def test_v3_join_rejects_unsealed_plain_objects(field: str) -> None:
    values = {
        "settlement": object(),
        "policy": object(),
        "data_availability": object(),
        "finality": object(),
        "durable_replay": object(),
    }
    values[field] = {"verified": True}

    with pytest.raises(TypeError):
        _bind_spot_v7_operational_commit_capability_v3(
            settlement=values["settlement"],
            policy=values["policy"],
            data_availability=values["data_availability"],
            finality=values["finality"],
            durable_replay=values["durable_replay"],
        )


def test_v3_join_rejects_missing_parent_header() -> None:
    settlement, policy, data_availability, finality, durable_replay, _parent = (
        _valid_prerequisites()
    )

    with pytest.raises(SpotV7OperationalCapabilityBindingErrorV3) as error:
        _bind_spot_v7_operational_commit_capability_v3(
            settlement=settlement,
            policy=policy,
            data_availability=data_availability,
            finality=finality,
            durable_replay=durable_replay,
        )

    assert error.value.code == "MISSING_PARENT_HEADER"


def test_v3_join_rejects_parent_header_with_wrong_hash() -> None:
    settlement, policy, data_availability, finality, durable_replay, parent = (
        _valid_prerequisites()
    )
    mutated_parent = parent.replace(b'"height":', b'"height":1', 1)

    with pytest.raises(SpotV7OperationalCapabilityBindingErrorV3) as error:
        _bind_spot_v7_operational_commit_capability_v3(
            settlement=settlement,
            policy=policy,
            data_availability=data_availability,
            finality=finality,
            durable_replay=durable_replay,
            exact_parent_header_bytes=mutated_parent,
        )

    assert error.value.code in {
        "PARENT_HEADER_BYTES_INVALID",
        "PARENT_HEADER_HASH_MISMATCH",
    }


@pytest.mark.parametrize(
    "operation",
    (
        copy.copy,
        copy.deepcopy,
        pickle.dumps,
    ),
)
def test_v3_capability_is_nontransferable(
    operation: Callable[[object], object],
) -> None:
    settlement, policy, data_availability, finality, durable_replay, parent = (
        _valid_prerequisites()
    )
    capability = _bind_spot_v7_operational_commit_capability_v3(
        settlement=settlement,
        policy=policy,
        data_availability=data_availability,
        finality=finality,
        durable_replay=durable_replay,
        exact_parent_header_bytes=parent,
    )

    with pytest.raises(TypeError):
        operation(capability)

    with pytest.raises(TypeError):
        capability._settlement = settlement
