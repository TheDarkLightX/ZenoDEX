"""CBC tests for settlement-envelope-bound Spot V7 finality V3."""

from __future__ import annotations

import copy
import hashlib
import inspect
import json
import pickle
from dataclasses import dataclass, replace
from typing import Any

import pytest

import src.integration._zrpf_spot_v7_operational_capability_v2 as operational_v2
import src.integration._zrpf_spot_v7_zeno_ledger_finality_contract as finality_contract
import src.integration.zrpf_spot_v7_zeno_ledger_finality_adapter as finality_adapter
import tests.integration.test_zrpf_spot_v7_settlement_envelope_replay as replay_test
import tests.integration.test_zrpf_spot_v7_zeno_ledger_finality_adapter as v2_test
from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _SpotV7SettlementCandidateInputV1,
)
from src.integration._zrpf_spot_v7_operational_capability_v2 import (
    _AuthenticatedExactCheckpointFinalityTransitionV2,
    _GovernedSpotV7OperationalPolicyV2,
)
from src.integration._zrpf_spot_v7_settlement_envelope_contract import (
    _AuthenticatedSpotV7SettlementReplayObservationV2,
)
from src.integration._zrpf_spot_v7_settlement_envelope_replay import (
    SpotV7SettlementEnvelopeReplayAdapterV2,
)
from src.integration._zrpf_spot_v7_zeno_ledger_finality_contract import (
    SPOT_V7_ZENO_LEDGER_FINALITY_EVIDENCE_SCHEMA_V3,
    ZenoLedgerCheckpointFinalityCursorV1,
    derive_zeno_ledger_finality_protocol_id_v2,
    derive_zeno_ledger_finality_protocol_id_v3,
)
from src.integration.dex_engine import DexEngineConfig
from src.integration.zeno_ledger_replay import replay_engine_config_document_v0
from src.integration.zeno_ledger_v0 import (
    ZERO_ROOT_V0,
    build_checkpoint_v0,
    build_header_v0,
    canonical_body_root_v0,
    canonical_header_hash_v0,
    compute_app_hash_v0,
    compute_evidence_root_v0,
    compute_ingress_root_v0,
    compute_tx_root_v0,
)
from src.integration.zrpf_spot_v7_zeno_ledger_finality_adapter import (
    SpotV7ZenoLedgerCheckpointFinalityAdapterV3,
    SpotV7ZenoLedgerFinalityBindingErrorV1,
)


@dataclass(frozen=True, slots=True)
class _V3Fixture:
    adapter: SpotV7ZenoLedgerCheckpointFinalityAdapterV3
    settlement: object
    replay_observation: _AuthenticatedSpotV7SettlementReplayObservationV2
    prior_cursor: ZenoLedgerCheckpointFinalityCursorV1
    checkpoint: dict[str, Any]
    validator_set: dict[str, Any]
    proposer_id: str
    proposer_key_id: str
    proposer_envelope: dict[str, Any]
    registry: dict[str, Any]
    envelopes: tuple[dict[str, Any], ...]


def _policy_v3(
    candidate: _SpotV7SettlementCandidateInputV1,
    registry: dict[str, Any],
    header: dict[str, Any],
    *,
    genesis_hash: str,
) -> _GovernedSpotV7OperationalPolicyV2:
    base = v2_test._policy(
        candidate,
        registry,
        header,
        genesis_hash=genesis_hash,
    )
    return _GovernedSpotV7OperationalPolicyV2(
        replace(
            base._material,
            finality_protocol_id=derive_zeno_ledger_finality_protocol_id_v3(),
        ),
        provenance=base._provenance,
        seal=operational_v2._GOVERNED_OPERATIONAL_POLICY_SEAL_V2,
    )


def _body_for_chain(body: dict[str, Any]) -> dict[str, Any]:
    body = json.loads(json.dumps(body))
    body["chain_id"] = v2_test.CHAIN_ID
    body["ingress"]["batch_cutoff"]["chain_id"] = v2_test.CHAIN_ID
    return body


def _header(
    *,
    candidate: object,
    body: dict[str, Any],
    validator_set: dict[str, Any],
    previous_hash: str,
) -> dict[str, Any]:
    config = replay_engine_config_document_v0(DexEngineConfig(chain_id=v2_test.CHAIN_ID))
    config_digest = v2_test.replay_engine_config_digest_v0(config)
    post_state_root = candidate.post_state_root  # type: ignore[attr-defined]
    evidence_root = compute_evidence_root_v0(body["evidence"])
    module_versions_digest = v2_test._root("modules-v3")
    app_hash = compute_app_hash_v0(
        {
            "chain_id": v2_test.CHAIN_ID,
            "height": candidate.epoch_id,  # type: ignore[attr-defined]
            "post_state_root": post_state_root,
            "evidence_root": evidence_root,
            "config_digest": config_digest,
            "module_versions_digest": module_versions_digest,
        }
    )
    return build_header_v0(
        chain_id=v2_test.CHAIN_ID,
        height=candidate.epoch_id,  # type: ignore[attr-defined]
        time_ms=1_784_000_000_001,
        prev_header_hash=previous_hash,
        sequencer_set_hash=validator_set["validator_set_hash"],
        ingress_root=compute_ingress_root_v0(body["ingress"]),
        tx_root=compute_tx_root_v0(body["transactions"]),
        pre_state_root=candidate.pre_state_root,  # type: ignore[attr-defined]
        post_state_root=post_state_root,
        app_hash=app_hash,
        evidence_root=evidence_root,
        body_root=canonical_body_root_v0(body),
        data_availability_root=candidate.data_root,  # type: ignore[attr-defined]
        proof_journal_hash=(
            "0x" + hashlib.sha256(candidate.exact_v7_journal_bytes).hexdigest()  # type: ignore[attr-defined]
        ),
        config_digest=config_digest,
        module_versions_digest=module_versions_digest,
        signature_set_root=ZERO_ROOT_V0,
    )


def _genesis_parent(candidate: object, validator_set: dict[str, Any]) -> dict[str, Any]:
    state_root = candidate.pre_state_root  # type: ignore[attr-defined]
    module_versions_digest = v2_test._root("genesis-modules-v3")
    config_digest = v2_test._root("genesis-config-v3")
    evidence_root = v2_test._root("genesis-evidence-v3")
    return build_header_v0(
        chain_id=v2_test.CHAIN_ID,
        height=0,
        time_ms=1_784_000_000_000,
        prev_header_hash=ZERO_ROOT_V0,
        sequencer_set_hash=validator_set["validator_set_hash"],
        ingress_root=v2_test._root("genesis-ingress-v3"),
        tx_root=v2_test._root("genesis-tx-v3"),
        pre_state_root=state_root,
        post_state_root=state_root,
        app_hash=compute_app_hash_v0(
            {
                "chain_id": v2_test.CHAIN_ID,
                "height": 0,
                "post_state_root": state_root,
                "evidence_root": evidence_root,
                "config_digest": config_digest,
                "module_versions_digest": module_versions_digest,
            }
        ),
        evidence_root=evidence_root,
        body_root=v2_test._root("genesis-body-v3"),
        data_availability_root=v2_test._root("genesis-da-v3"),
        proof_journal_hash=v2_test._root("genesis-proof-v3"),
        config_digest=config_digest,
        module_versions_digest=module_versions_digest,
        signature_set_root=ZERO_ROOT_V0,
    )


def _fixture(*, nonzero_parent: bool = False) -> _V3Fixture:
    replay = replay_test._fixture()
    candidate = replay.candidate
    settlement = replay.settlement
    body = _body_for_chain(replay.body)
    validator_set = v2_test._validator_set()
    parent = _genesis_parent(candidate, validator_set) if nonzero_parent else None
    prior_hash = ZERO_ROOT_V0 if parent is None else canonical_header_hash_v0(parent)
    header = _header(
        candidate=candidate,
        body=body,
        validator_set=validator_set,
        previous_hash=prior_hash,
    )
    config = replay_engine_config_document_v0(DexEngineConfig(chain_id=v2_test.CHAIN_ID))
    replay_observation = SpotV7SettlementEnvelopeReplayAdapterV2(config).authenticate(
        settlement=settlement,
        header=header,
        body=body,
        pre_snapshot=replay.pre_snapshot,
        parent_header=parent,
    )
    registry = v2_test._registry()
    policy = _policy_v3(candidate, registry, header, genesis_hash=prior_hash)
    checkpoint = build_checkpoint_v0(header)
    duty = v2_test.build_proposer_duty_v0(
        validator_set=validator_set,
        height=candidate.epoch_id,
    )
    proposer = duty["proposer"]
    assert isinstance(proposer, dict)
    return _V3Fixture(
        adapter=SpotV7ZenoLedgerCheckpointFinalityAdapterV3(policy),
        settlement=settlement,
        replay_observation=replay_observation,
        prior_cursor=ZenoLedgerCheckpointFinalityCursorV1(0, prior_hash),
        checkpoint=checkpoint,
        validator_set=validator_set,
        proposer_id=str(proposer["validator_id"]),
        proposer_key_id=str(proposer["key_id"]),
        proposer_envelope=v2_test._proposer_envelope(
            str(checkpoint["header_hash"]),
            validator_set,
        ),
        registry=registry,
        envelopes=v2_test._envelopes(str(checkpoint["header_hash"])),
    )


def _authenticate(fixture: _V3Fixture) -> object:
    return fixture.adapter.authenticate(
        settlement=fixture.settlement,
        prior_cursor=fixture.prior_cursor,
        settlement_replay_observation=fixture.replay_observation,
        checkpoint=fixture.checkpoint,
        validator_set=fixture.validator_set,
        proposer_id=fixture.proposer_id,
        proposer_key_id=fixture.proposer_key_id,
        proposer_envelope=fixture.proposer_envelope,
        registry=fixture.registry,
        envelopes=fixture.envelopes,
    )


def test_v3_identity_is_distinct_from_transaction_replay_v2() -> None:
    assert derive_zeno_ledger_finality_protocol_id_v3() != (
        derive_zeno_ledger_finality_protocol_id_v2()
    )


def test_v3_derives_header_from_exact_settlement_replay_observation() -> None:
    fixture = _fixture()

    capability = _authenticate(fixture)

    evidence = json.loads(capability._exact_finality_evidence_bytes)  # type: ignore[attr-defined]
    assert type(capability) is not _AuthenticatedExactCheckpointFinalityTransitionV2
    assert type(capability).__name__ == "_AuthenticatedExactCheckpointFinalityTransitionV3"
    assert capability.proof_receipt_authentication_established is False  # type: ignore[attr-defined]
    assert capability.exact_replay_material_authenticated is True  # type: ignore[attr-defined]
    assert capability.durable_settlement_replay_material_persisted is False  # type: ignore[attr-defined]
    assert capability.durable_settlement_replay_reverified is False  # type: ignore[attr-defined]
    assert capability.hostile_same_interpreter_resistance_established is False  # type: ignore[attr-defined]
    assert capability.settlement_authority is False  # type: ignore[attr-defined]
    assert capability.production_authority is False  # type: ignore[attr-defined]
    projection = fixture.replay_observation._projection_for_finality_adapter()
    assert evidence["schema"] == SPOT_V7_ZENO_LEDGER_FINALITY_EVIDENCE_SCHEMA_V3
    assert evidence["settlement_replay_observation"] == (
        fixture.replay_observation._canonical_projection_for_finality_adapter()
    )
    assert evidence["settlement_replay_observation"]["receipt_accepted"] is True
    assert evidence["settlement_replay_observation"]["replay_material_root"] == (
        projection.replay_material_root
    )
    assert evidence["settlement_replay_observation"]["economic_action_id"] == (
        projection.economic_action_id
    )
    assert "header" not in inspect.signature(fixture.adapter.authenticate).parameters
    assert fixture.adapter.proof_receipt_authentication_established is False
    assert fixture.adapter.application_domain_to_ledger_chain_binding_established is False
    assert fixture.adapter.public_data_retrievability_established is False
    assert fixture.adapter.canonical_conflicting_checkpoint_selection_established is False
    assert fixture.adapter.exact_replay_material_authenticated is True
    assert fixture.adapter.durable_settlement_replay_material_persisted is False
    assert fixture.adapter.durable_settlement_replay_reverified is False
    assert fixture.adapter.hostile_same_interpreter_resistance_established is False
    assert evidence["claims"]["exact_replay_material_authenticated"] is True
    assert evidence["claims"]["replay_material_commitment_bound"] is True
    assert evidence["claims"]["durable_settlement_replay_material_persisted"] is False
    assert evidence["claims"]["durable_settlement_replay_reverified"] is False
    assert evidence["claims"]["hostile_same_interpreter_resistance_established"] is False
    assert fixture.adapter.release_authority is False
    assert fixture.adapter.settlement_authority is False
    assert fixture.adapter.production_authority is False


def test_v3_accepts_an_exact_nonzero_genesis_parent() -> None:
    fixture = _fixture(nonzero_parent=True)

    capability = _authenticate(fixture)

    evidence = json.loads(capability._exact_finality_evidence_bytes)  # type: ignore[attr-defined]
    assert evidence["settlement_replay_observation"]["parent_header_hash"] == (
        fixture.prior_cursor.checkpoint_hash
    )


def test_v3_transition_rejects_copy_pickle_and_mutation() -> None:
    capability = _authenticate(_fixture())

    with pytest.raises(TypeError):
        copy.copy(capability)
    with pytest.raises(TypeError):
        copy.deepcopy(capability)
    with pytest.raises(TypeError):
        pickle.dumps(capability)
    with pytest.raises(TypeError):
        capability._projection = capability._projection  # type: ignore[attr-defined]


def test_v3_authenticates_the_checkpoint_quorum_exactly_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture()
    observed = 0
    original = finality_adapter.build_live_checkpoint_quorum_admission_v0

    def counted(**kwargs: object) -> dict[str, Any]:
        nonlocal observed
        observed += 1
        return original(**kwargs)

    monkeypatch.setattr(
        finality_adapter,
        "build_live_checkpoint_quorum_admission_v0",
        counted,
    )

    _authenticate(fixture)

    assert observed == 1


def test_v3_rejects_the_transaction_only_finality_v2_observation_type() -> None:
    fixture = _fixture()
    old = v2_test._fixture().replay_observation

    with pytest.raises(TypeError, match="exact private V2 observation"):
        fixture.adapter.authenticate(
            settlement=fixture.settlement,
            prior_cursor=fixture.prior_cursor,
            settlement_replay_observation=old,
            checkpoint=fixture.checkpoint,
            validator_set=fixture.validator_set,
            proposer_id=fixture.proposer_id,
            proposer_key_id=fixture.proposer_key_id,
            proposer_envelope=fixture.proposer_envelope,
            registry=fixture.registry,
            envelopes=fixture.envelopes,
        )


def test_v3_rejects_a_different_settlement_for_the_sealed_observation() -> None:
    fixture = _fixture()
    candidate = fixture.settlement._candidate_for_atomic_store()  # type: ignore[attr-defined]
    substituted = replace(
        candidate,
        authorization_nullifier=v2_test._root("substituted-authorization-v3"),
    )

    with pytest.raises(SpotV7ZenoLedgerFinalityBindingErrorV1) as captured:
        fixture.adapter.authenticate(
            settlement=v2_test._settlement(substituted),
            prior_cursor=fixture.prior_cursor,
            settlement_replay_observation=fixture.replay_observation,
            checkpoint=fixture.checkpoint,
            validator_set=fixture.validator_set,
            proposer_id=fixture.proposer_id,
            proposer_key_id=fixture.proposer_key_id,
            proposer_envelope=fixture.proposer_envelope,
            registry=fixture.registry,
            envelopes=fixture.envelopes,
        )

    assert captured.value.code == "replay_candidate_settlement"


@pytest.mark.parametrize(
    ("field_name", "replacement"),
    (
        (
            "SPOT_V7_SETTLEMENT_ENVELOPE_PROFILE_V1",
            "restricted_singleton_spot_state_root_test_mutation",
        ),
        (
            "SPOT_V7_SETTLEMENT_REPLAY_OBSERVATION_PROFILE_V2",
            "exact_retained_replay_test_mutation",
        ),
        (
            "SPOT_V7_SETTLEMENT_REPLAY_MATERIAL_ROOT_DOMAIN_V2",
            "zrpf_spot_v7_settlement_replay_material_test_mutation",
        ),
    ),
)
def test_v3_protocol_identity_binds_settlement_replay_contract(
    monkeypatch: pytest.MonkeyPatch,
    field_name: str,
    replacement: str,
) -> None:
    expected_v2 = derive_zeno_ledger_finality_protocol_id_v2()
    expected_v3 = derive_zeno_ledger_finality_protocol_id_v3()

    monkeypatch.setattr(
        finality_contract,
        field_name,
        replacement,
    )

    assert derive_zeno_ledger_finality_protocol_id_v2() == expected_v2
    assert derive_zeno_ledger_finality_protocol_id_v3() != expected_v3
