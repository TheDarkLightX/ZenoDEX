"""CBC tests for the governed ZenoLedger checkpoint-finality adapter."""

from __future__ import annotations

import copy
import hashlib
import json
import pickle
from dataclasses import dataclass, replace
from typing import NoReturn

import pytest
from py_ecc.optimized_bls12_381 import curve_order

import src.integration._zrpf_spot_v7_firecracker_authority as firecracker_authority
import src.integration._zrpf_spot_v7_operational_capability_v2 as operational_v2
import src.integration._zrpf_spot_v7_zeno_ledger_finality_contract as finality_contract
import src.integration.zrpf_spot_v7_zeno_ledger_finality_adapter as adapter_module
from src.core.dex import DexState
from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _SpotV7SettlementCandidateInputV1,
)
from src.integration._zrpf_spot_v7_firecracker_authority import (
    _GovernedFirecrackerSpotV7SettlementV1,
)
from src.integration._zrpf_spot_v7_operational_capability_v2 import (
    _AuthenticatedExactCheckpointFinalityTransitionV2,
    _GovernedOperationalPolicyMaterialV2,
    _GovernedOperationalPolicyProvenanceV1,
    _GovernedSpotV7OperationalPolicyV2,
)
from src.integration._zrpf_spot_v7_zeno_ledger_replay_contract import (
    SPOT_V7_ZENO_LEDGER_BODY_PROOF_RECEIPT_PROJECTION_SCHEMA_V1,
)
from src.integration._zrpf_spot_v7_zeno_ledger_replay_observation import (
    SpotV7ZenoLedgerReplayBoundObservationAdapterV1,
    _AuthenticatedReplayBoundBlockObservationV1,
)
from src.integration.dex_engine import DexEngineConfig
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.zeno_ledger_replay import (
    replay_engine_config_digest_v0,
    replay_engine_config_document_v0,
)
from src.integration.zeno_ledger_signature import (
    bls_public_key_hex_from_private_key_v0,
    build_bls_signed_artifact_envelope_v0,
)
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0
from src.integration.zeno_ledger_v0 import (
    BATCH_CUTOFF_SCHEMA_V0,
    BODY_SCHEMA_V0,
    build_checkpoint_v0,
    build_header_v0,
    canonical_body_root_v0,
    canonical_json_bytes_v0,
    compute_app_hash_v0,
    compute_evidence_root_v0,
    compute_ingress_root_v0,
    compute_tx_root_v0,
    dex_state_root_v0,
    hash_v0,
)
from src.integration.zeno_ledger_v0 import (
    VALIDATOR_SET_SCHEMA_V0 as LEDGER_VALIDATOR_SET_SCHEMA_V0,
)
from src.integration.zeno_ledger_validator_schedule_v0 import (
    build_proposer_duty_v0,
    build_validator_set_v0,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    SpotV7AssetEffectV1,
    SpotV7CellKindV1,
    SpotV7CellOpeningV1,
    SpotV7CellRoleV1,
    SpotV7CellTransitionV1,
    spot_v7_cell_transitions_root_v1,
)
from src.integration.zrpf_spot_v7_zeno_ledger_finality_adapter import (
    SPOT_V7_ZENO_LEDGER_FINALITY_EVIDENCE_SCHEMA_V2,
    SpotV7ZenoLedgerCheckpointFinalityAdapterV2,
    SpotV7ZenoLedgerFinalityBindingErrorV1,
    ZenoLedgerCheckpointFinalityCursorV1,
    derive_zeno_ledger_external_finality_policy_hash_v2,
    derive_zeno_ledger_finality_network_id_v1,
    derive_zeno_ledger_finality_protocol_id_v2,
    derive_zeno_ledger_proposer_authorship_payload_hash_v1,
)
from src.state.balances import BalanceTable
from src.state.lp import LPTable

ZERO_ROOT = "0x" + "00" * 32
CHAIN_ID = "zeno-ledger-zrpf-finality-test-v1"


@dataclass(frozen=True, slots=True)
class _FinalityFixture:
    adapter: SpotV7ZenoLedgerCheckpointFinalityAdapterV2
    settlement: _GovernedFirecrackerSpotV7SettlementV1
    prior_cursor: ZenoLedgerCheckpointFinalityCursorV1
    replay_observation: _AuthenticatedReplayBoundBlockObservationV1
    header: dict[str, object]
    checkpoint: dict[str, object]
    validator_set: dict[str, object]
    proposer_id: str
    proposer_key_id: str
    proposer_envelope: dict[str, object]
    registry: dict[str, object]
    envelopes: tuple[dict[str, object], ...]


def _root(label: str) -> str:
    return hash_v0("zrpf_spot_v7_finality_adapter_test_root", {"label": label})


def _private_key(label: str) -> str:
    raw = int.from_bytes(hashlib.sha256(label.encode("ascii")).digest(), "big")
    value = (raw % (int(curve_order) - 1)) + 1
    return "0x" + value.to_bytes(32, "big").hex()


def _fixed_bytes(label: str, length: int) -> bytes:
    output = bytearray()
    counter = 0
    while len(output) < length:
        output.extend(hashlib.sha256(f"{label}:{counter}".encode("ascii")).digest())
        counter += 1
    return bytes(output[:length])


def _opening(
    kind: SpotV7CellKindV1,
    subject_id: str,
    asset_id: str,
    atoms: int,
) -> SpotV7CellOpeningV1:
    return SpotV7CellOpeningV1(kind, subject_id, asset_id, atoms)


def _empty_state() -> DexState:
    return DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())


def _candidate(*, epoch_id: int = 1) -> _SpotV7SettlementCandidateInputV1:
    sender = "0x" + _fixed_bytes("sender", 48).hex()
    recipient = "0x" + _fixed_bytes("recipient", 48).hex()
    pool = _root("pool")
    input_asset = _root("input-asset")
    output_asset = _root("output-asset")
    action = _root("action")
    transitions = tuple(
        sorted(
            (
                SpotV7CellTransitionV1(
                    SpotV7CellRoleV1.DEBIT,
                    _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, sender, input_asset, 1_000),
                    _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, sender, input_asset, 900),
                ),
                SpotV7CellTransitionV1(
                    SpotV7CellRoleV1.CREDIT,
                    _opening(SpotV7CellKindV1.POOL_RESERVE, pool, input_asset, 5_000),
                    _opening(SpotV7CellKindV1.POOL_RESERVE, pool, input_asset, 5_100),
                ),
                SpotV7CellTransitionV1(
                    SpotV7CellRoleV1.DEBIT,
                    _opening(SpotV7CellKindV1.POOL_RESERVE, pool, output_asset, 8_000),
                    _opening(SpotV7CellKindV1.POOL_RESERVE, pool, output_asset, 7_940),
                ),
                SpotV7CellTransitionV1(
                    SpotV7CellRoleV1.CREDIT,
                    _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, recipient, output_asset, 25),
                    _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, recipient, output_asset, 85),
                ),
            ),
            key=lambda row: row.cell_key,
        )
    )
    effects = tuple(
        sorted(
            (
                SpotV7AssetEffectV1(action, input_asset, 100),
                SpotV7AssetEffectV1(action, output_asset, 60),
            ),
            key=lambda row: (row.asset_id, row.effect_id),
        )
    )
    state_root = dex_state_root_v0(_empty_state())
    return _SpotV7SettlementCandidateInputV1(
        application_id=_root("application"),
        chain_or_domain_id=_root("domain"),
        epoch_id=epoch_id,
        verified_program_id=_root("program"),
        verified_profile_id=_root("profile"),
        verified_program_manifest_root=_root("manifest"),
        source_child_claim_binding=_root("child-claim"),
        source_child_journal_sha256=_root("child-journal"),
        data_availability_certificate_root=_root("da-certificate"),
        data_root=_root("data"),
        settlement_effect_plan_commitment=_root("plan"),
        pre_state_root=state_root,
        post_state_root=state_root,
        economic_action_id=action,
        authorization_nullifier=_root("authorization"),
        authorization_grant_spend_nullifier=_root("grant-spend"),
        consumed_object_ids=(_root("consumed"),),
        cell_transitions=transitions,
        cell_transitions_root=spot_v7_cell_transitions_root_v1(transitions),
        asset_effects=effects,
        exact_v7_receipt_bytes=b"exact-v7-receipt",
        exact_v7_journal_bytes=b"exact-v7-journal",
        exact_plan_b_bytes=b"exact-v7-plan",
        exact_firecracker_execution_record_bytes=b"exact-firecracker-record",
        exact_firecracker_output_bytes=b"exact-firecracker-output",
    )


def _settlement(
    candidate: _SpotV7SettlementCandidateInputV1,
) -> _GovernedFirecrackerSpotV7SettlementV1:
    capability = object.__new__(_GovernedFirecrackerSpotV7SettlementV1)
    object.__setattr__(capability, "_candidate", candidate)
    object.__setattr__(capability, "_runtime_execution", object())
    object.__setattr__(capability, "_seal", firecracker_authority._GOVERNED_BINDER_SEAL_V1)
    return capability


def _registry(*, threshold: int = 2) -> dict[str, object]:
    keys = (_private_key("validator-a"), _private_key("validator-b"))
    return build_signer_registry_v0(
        registry_id="zrpf-finality-validator-set-v1",
        payload_kind="checkpoint",
        threshold=threshold,
        signers=[
            {
                "signer_id": f"validator-{index}",
                "key_id": f"bls-{index}",
                "public_key": bls_public_key_hex_from_private_key_v0(key),
                "weight": 1,
                "status": "active",
            }
            for index, key in enumerate(keys)
        ],
    )


def _validator_set() -> dict[str, object]:
    keys = (_private_key("sequencer-a"), _private_key("sequencer-b"))
    return build_validator_set_v0(
        chain_id=CHAIN_ID,
        epoch=0,
        start_height=1,
        validators=[
            {
                "validator_id": f"sequencer-{index}",
                "key_id": f"sequencer-bls-{index}",
                "public_key": bls_public_key_hex_from_private_key_v0(key),
                "voting_power": 1,
                "status": "active",
            }
            for index, key in enumerate(keys)
        ],
    )


def _ledger_body(
    candidate: _SpotV7SettlementCandidateInputV1,
    *,
    body_proof_journal_hash: str | None = None,
) -> dict[str, object]:
    return {
        "schema": BODY_SCHEMA_V0,
        "chain_id": CHAIN_ID,
        "height": candidate.epoch_id,
        "ingress": {
            "batch_cutoff": {
                "schema": BATCH_CUTOFF_SCHEMA_V0,
                "chain_id": CHAIN_ID,
                "height": candidate.epoch_id,
                "cutoff_time_ms": 1_784_000_000_000 + candidate.epoch_id,
                "cutoff_sequence": candidate.epoch_id,
                "sequencer_id": "sequencer-0",
                "policy_id": "bounded-replay-v0",
                "policy_digest": _root("ingress-policy"),
            },
            "ingress_receipts": [],
            "forced_inclusion_requests": [],
            "forced_inclusion_decisions": [],
        },
        "transactions": [],
        "settlement_envelopes": [],
        "evidence": {
            "upba_certificates": [],
            "price_grid_tables": [],
            "uniform_batch_hypergraph_roots": [],
            "oracle_packets": [],
            "proof_receipts": [
                {
                    "schema": (
                        SPOT_V7_ZENO_LEDGER_BODY_PROOF_RECEIPT_PROJECTION_SCHEMA_V1
                    ),
                    "proof_journal_hash": (
                        body_proof_journal_hash
                        or "0x"
                        + hashlib.sha256(candidate.exact_v7_journal_bytes).hexdigest()
                    )
                }
            ],
            "rejection_receipts": [],
        },
    }


def _engine_config_document() -> dict[str, object]:
    return replay_engine_config_document_v0(DexEngineConfig(chain_id=CHAIN_ID))


def _replay_observation(
    candidate: _SpotV7SettlementCandidateInputV1,
    header: dict[str, object],
    *,
    parent_header: dict[str, object] | None = None,
    body_proof_journal_hash: str | None = None,
) -> _AuthenticatedReplayBoundBlockObservationV1:
    return SpotV7ZenoLedgerReplayBoundObservationAdapterV1(
        _engine_config_document()
    ).authenticate(
        header=header,
        body=_ledger_body(
            candidate,
            body_proof_journal_hash=body_proof_journal_hash,
        ),
        pre_snapshot=snapshot_from_state(_empty_state()).data,
        parent_header=parent_header,
    )


def _header(
    candidate: _SpotV7SettlementCandidateInputV1,
    validator_set: dict[str, object],
    *,
    previous_hash: str,
    proof_journal_hash: str | None = None,
    post_state_root: str | None = None,
    app_hash: str | None = None,
    body_proof_journal_hash: str | None = None,
) -> dict[str, object]:
    checked_post_state_root = post_state_root or candidate.post_state_root
    body = _ledger_body(
        candidate,
        body_proof_journal_hash=body_proof_journal_hash,
    )
    evidence = body["evidence"]
    ingress = body["ingress"]
    transactions = body["transactions"]
    assert isinstance(evidence, dict)
    assert isinstance(ingress, dict)
    assert isinstance(transactions, list)
    evidence_root = compute_evidence_root_v0(evidence)
    config_digest = replay_engine_config_digest_v0(_engine_config_document())
    module_versions_digest = _root("modules")
    checked_app_hash = app_hash or compute_app_hash_v0(
        {
            "chain_id": CHAIN_ID,
            "height": candidate.epoch_id,
            "post_state_root": checked_post_state_root,
            "evidence_root": evidence_root,
            "config_digest": config_digest,
            "module_versions_digest": module_versions_digest,
        }
    )
    return build_header_v0(
        chain_id=CHAIN_ID,
        height=candidate.epoch_id,
        time_ms=1_784_000_000_000 + candidate.epoch_id,
        prev_header_hash=previous_hash,
        sequencer_set_hash=str(validator_set["validator_set_hash"]),
        ingress_root=compute_ingress_root_v0(ingress),
        tx_root=compute_tx_root_v0(transactions),
        pre_state_root=candidate.pre_state_root,
        post_state_root=checked_post_state_root,
        app_hash=checked_app_hash,
        evidence_root=evidence_root,
        body_root=canonical_body_root_v0(body),
        data_availability_root=candidate.data_root,
        proof_journal_hash=proof_journal_hash
        or "0x" + hashlib.sha256(candidate.exact_v7_journal_bytes).hexdigest(),
        config_digest=config_digest,
        module_versions_digest=module_versions_digest,
        signature_set_root=ZERO_ROOT,
    )


def _policy(
    candidate: _SpotV7SettlementCandidateInputV1,
    registry: dict[str, object],
    header: dict[str, object],
    *,
    genesis_hash: str,
    policy_revocation_epoch: int | None = None,
) -> _GovernedSpotV7OperationalPolicyV2:
    material = _GovernedOperationalPolicyMaterialV2(
        application_id=candidate.application_id,
        chain_or_domain_id=candidate.chain_or_domain_id,
        data_schema_id=_root("data-schema"),
        storage_policy_hash=_root("storage-policy"),
        minimum_retention_epochs=10,
        minimum_remaining_epochs=2,
        maximum_blob_bytes=1_024 * 1_024,
        finality_network_id=derive_zeno_ledger_finality_network_id_v1(CHAIN_ID),
        finality_protocol_id=derive_zeno_ledger_finality_protocol_id_v2(),
        external_finality_policy_hash=(
            derive_zeno_ledger_external_finality_policy_hash_v2(
                chain_id=CHAIN_ID,
                config_digest=str(header["config_digest"]),
                sequencer_set_hash=str(header["sequencer_set_hash"]),
            )
        ),
        finality_verifier_set_root=str(registry["registry_hash"]),
        genesis_application_checkpoint_sequence=0,
        genesis_application_checkpoint_hash=genesis_hash,
    )
    provenance_bytes = b'{"schema":"test-only-operational-policy-provenance-v1"}'
    return _GovernedSpotV7OperationalPolicyV2(
        material,
        provenance=_GovernedOperationalPolicyProvenanceV1(
            evidence_root="0x" + hashlib.sha256(provenance_bytes).hexdigest(),
            exact_evidence_bytes=provenance_bytes,
            manifest_sha256=hashlib.sha256(b"test-only-manifest").hexdigest(),
            signer_registry_hash=_root("test-only-policy-registry"),
            signature_quorum_report_hash=_root("test-only-policy-quorum"),
            policy_revision=1,
            policy_activation_epoch=0,
            policy_revocation_epoch=policy_revocation_epoch,
            signer_registry_revision=1,
            signer_registry_activation_epoch=0,
            signer_registry_revocation_epoch=None,
            evaluation_epoch=0,
        ),
        seal=operational_v2._GOVERNED_OPERATIONAL_POLICY_SEAL_V2,
    )


def _envelopes(header_hash: str) -> tuple[dict[str, object], ...]:
    return tuple(
        build_bls_signed_artifact_envelope_v0(
            payload_kind="checkpoint",
            payload_hash=header_hash,
            signer_id=f"validator-{index}",
            key_id=f"bls-{index}",
            private_key_hex=_private_key(label),
        )
        for index, label in enumerate(("validator-a", "validator-b"))
    )


def _proposer_envelope(
    header_hash: str,
    validator_set: dict[str, object],
    *,
    height: int = 1,
    proposer_index: int = 0,
) -> dict[str, object]:
    duty = build_proposer_duty_v0(validator_set=validator_set, height=height)
    payload_hash = derive_zeno_ledger_proposer_authorship_payload_hash_v1(
        chain_id=str(validator_set["chain_id"]),
        height=height,
        header_hash=header_hash,
        validator_set_hash=str(validator_set["validator_set_hash"]),
        duty_hash=str(duty["duty_hash"]),
    )
    return build_bls_signed_artifact_envelope_v0(
        payload_kind="checkpoint",
        payload_hash=payload_hash,
        signer_id=f"sequencer-{proposer_index}",
        key_id=f"sequencer-bls-{proposer_index}",
        private_key_hex=_private_key(("sequencer-a", "sequencer-b")[proposer_index]),
    )


def _fixture() -> _FinalityFixture:
    candidate = _candidate()
    registry = _registry()
    validator_set = _validator_set()
    genesis_hash = _root("checkpoint-genesis")
    header = _header(candidate, validator_set, previous_hash=genesis_hash)
    checkpoint = build_checkpoint_v0(header)
    policy = _policy(candidate, registry, header, genesis_hash=genesis_hash)
    duty = build_proposer_duty_v0(
        validator_set=validator_set,
        height=candidate.epoch_id,
    )
    proposer = duty["proposer"]
    assert isinstance(proposer, dict)
    return _FinalityFixture(
        adapter=SpotV7ZenoLedgerCheckpointFinalityAdapterV2(policy),
        settlement=_settlement(candidate),
        prior_cursor=ZenoLedgerCheckpointFinalityCursorV1(
            sequence=0,
            checkpoint_hash=genesis_hash,
        ),
        replay_observation=_replay_observation(candidate, header),
        header=header,
        checkpoint=checkpoint,
        validator_set=validator_set,
        proposer_id=str(proposer["validator_id"]),
        proposer_key_id=str(proposer["key_id"]),
        proposer_envelope=_proposer_envelope(
            str(checkpoint["header_hash"]),
            validator_set,
        ),
        registry=registry,
        envelopes=_envelopes(str(checkpoint["header_hash"])),
    )


def _authenticate(fixture: _FinalityFixture) -> _AuthenticatedExactCheckpointFinalityTransitionV2:
    return fixture.adapter.authenticate(
        settlement=fixture.settlement,
        prior_cursor=fixture.prior_cursor,
        header=fixture.header,
        replay_observation=fixture.replay_observation,
        checkpoint=fixture.checkpoint,
        validator_set=fixture.validator_set,
        proposer_id=fixture.proposer_id,
        proposer_key_id=fixture.proposer_key_id,
        proposer_envelope=fixture.proposer_envelope,
        registry=fixture.registry,
        envelopes=fixture.envelopes,
    )


def test_valid_governed_bls_quorum_mints_exact_checkpoint_finality_v2() -> None:
    fixture = _fixture()
    capability = _authenticate(fixture)
    candidate = fixture.settlement._candidate_for_atomic_store()

    assert type(capability) is _AuthenticatedExactCheckpointFinalityTransitionV2
    assert capability._has_private_seal() is True
    assert capability._projection.application_id == candidate.application_id
    assert capability._projection.chain_or_domain_id == candidate.chain_or_domain_id
    assert capability._projection.epoch_id == candidate.epoch_id
    assert capability._projection.proof_journal_hash == (
        "0x" + hashlib.sha256(candidate.exact_v7_journal_bytes).hexdigest()
    )
    assert capability._projection.post_state_root == candidate.post_state_root
    assert (
        capability._projection.prior_application_checkpoint_sequence
        == fixture.prior_cursor.sequence
    )
    assert (
        capability._projection.prior_application_checkpoint_hash
        == fixture.prior_cursor.checkpoint_hash
    )
    assert capability._projection.next_application_checkpoint_sequence == 1
    assert (
        capability._projection.next_application_checkpoint_hash == fixture.checkpoint["header_hash"]
    )
    assert capability._projection.finality_evidence_root == (
        "0x" + hashlib.sha256(capability._exact_finality_evidence_bytes).hexdigest()
    )
    evidence = json.loads(capability._exact_finality_evidence_bytes)
    assert evidence["schema"] == SPOT_V7_ZENO_LEDGER_FINALITY_EVIDENCE_SCHEMA_V2
    assert evidence["registry"]["registry_hash"] == fixture.registry["registry_hash"]
    assert (
        evidence["validator_set"]["validator_set_hash"]
        == (fixture.validator_set["validator_set_hash"])
    )
    assert fixture.registry["registry_hash"] != fixture.validator_set["validator_set_hash"]
    assert (
        evidence["scheduled_header_admission"]["validator_set_hash"]
        == (fixture.header["sequencer_set_hash"])
    )
    assert evidence["proposer_authorship_admission"]["proposer_id"] == (fixture.proposer_id)
    assert (
        evidence["proposer_authorship_admission"]["envelope_hash"]
        == (fixture.proposer_envelope["envelope_hash"])
    )
    assert (
        evidence["proposer_authorship_admission"]["authorship_payload_hash"]
        == (fixture.proposer_envelope["payload_hash"])
    )
    assert fixture.proposer_envelope["payload_hash"] != fixture.checkpoint["header_hash"]
    assert evidence["live_quorum_admission"]["accepted_weight"] == 2
    replay = evidence["replay_bound_observation"]
    assert replay["header_hash"] == fixture.checkpoint["header_hash"]
    assert replay["body_root"] == fixture.header["body_root"]
    assert replay["config_digest"] == fixture.header["config_digest"]
    assert replay["pre_state_root"] == candidate.pre_state_root
    assert replay["post_state_root"] == candidate.post_state_root
    assert replay["replayed_receipt_count"] == 0
    assert replay["replayed_rejection_count"] == 0
    assert replay["committed_proof_receipt_count"] == 1
    assert canonical_json_bytes_v0(evidence) == capability._exact_finality_evidence_bytes

def test_finality_rejects_policy_reuse_at_its_revocation_epoch() -> None:
    fixture = _fixture()
    candidate = fixture.settlement._candidate_for_atomic_store()
    policy = _policy(
        candidate,
        fixture.registry,
        fixture.header,
        genesis_hash=fixture.prior_cursor.checkpoint_hash,
        policy_revocation_epoch=candidate.epoch_id,
    )
    expired = replace(
        fixture,
        adapter=SpotV7ZenoLedgerCheckpointFinalityAdapterV2(policy),
    )

    with pytest.raises(SpotV7ZenoLedgerFinalityBindingErrorV1) as captured:
        _authenticate(expired)

    assert captured.value.code == "operational_policy_inactive"


@pytest.mark.parametrize(
    ("constant_name", "replacement"),
    (
        (
            "SCHEDULED_VALIDATOR_SET_SCHEMA_V1",
            "zenodex/zeno_ledger/scheduled_validator_set/test-mutation",
        ),
        ("SCHEDULED_VALIDATOR_SET_HASH_DOMAIN_V1", "scheduled_validator_set_test_mutation"),
        (
            "SCHEDULED_VALIDATOR_ENTRY_HASH_DOMAIN_V1",
            "scheduled_validator_set_entry_test_mutation",
        ),
    ),
)
def test_finality_protocol_identity_binds_scheduled_validator_set_contract(
    constant_name: str,
    replacement: str,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    expected = derive_zeno_ledger_finality_protocol_id_v2()

    monkeypatch.setattr(finality_contract, constant_name, replacement)

    assert derive_zeno_ledger_finality_protocol_id_v2() != expected


@pytest.mark.parametrize(
    ("constant_name", "replacement"),
    (
        (
            "SPOT_V7_ZENO_LEDGER_REPLAY_OBSERVATION_SCHEMA_V1",
            "zenodex/zrpf/spot_v7/zeno_ledger_replay_bound_observation/test-mutation",
        ),
        (
            "SPOT_V7_ZENO_LEDGER_RECEIPTS_ROOT_DOMAIN_V1",
            "zrpf_spot_v7_zeno_ledger_replayed_receipts_test_mutation",
        ),
        (
            "SPOT_V7_ZENO_LEDGER_CONFIG_DOCUMENT_ROOT_DOMAIN_V1",
            "zrpf_spot_v7_zeno_ledger_config_document_test_mutation",
        ),
        (
            "SPOT_V7_ZENO_LEDGER_REJECTIONS_ROOT_DOMAIN_V1",
            "zrpf_spot_v7_zeno_ledger_replayed_rejections_test_mutation",
        ),
        (
            "SPOT_V7_ZENO_LEDGER_PROOF_RECEIPTS_ROOT_DOMAIN_V1",
            "zrpf_spot_v7_zeno_ledger_committed_proof_receipts_test_mutation",
        ),
        (
            "SPOT_V7_ZENO_LEDGER_BODY_PROOF_RECEIPT_PROJECTION_SCHEMA_V1",
            "zenodex/zrpf/spot_v7/zeno_ledger_body_proof_receipt_projection/test",
        ),
        ("SPOT_V7_ZENO_LEDGER_BODY_PROOF_RECEIPT_COUNT_V1", 2),
        ("MAX_SPOT_V7_ZENO_LEDGER_REPLAY_RECEIPTS_V1", 65_535),
    ),
)
def test_finality_protocol_identity_binds_replay_observation_contract(
    constant_name: str,
    replacement: object,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    expected = derive_zeno_ledger_finality_protocol_id_v2()

    monkeypatch.setattr(finality_contract, constant_name, replacement)

    assert derive_zeno_ledger_finality_protocol_id_v2() != expected


def test_signature_order_does_not_change_canonical_finality_evidence() -> None:
    fixture = _fixture()
    first = _authenticate(fixture)
    second = fixture.adapter.authenticate(
        settlement=fixture.settlement,
        prior_cursor=fixture.prior_cursor,
        header=fixture.header,
        replay_observation=fixture.replay_observation,
        checkpoint=fixture.checkpoint,
        validator_set=fixture.validator_set,
        proposer_id=fixture.proposer_id,
        proposer_key_id=fixture.proposer_key_id,
        proposer_envelope=fixture.proposer_envelope,
        registry=fixture.registry,
        envelopes=tuple(reversed(fixture.envelopes)),
    )

    assert second._exact_finality_evidence_bytes == first._exact_finality_evidence_bytes
    assert second._exact_certificate_bytes == first._exact_certificate_bytes
    assert second._projection == first._projection


def test_weighted_schedule_uses_the_height_selected_proposer_key() -> None:
    candidate = _candidate(epoch_id=2)
    registry = _registry()
    validator_set = _validator_set()
    genesis_hash = _root("checkpoint-genesis")
    parent_header = _header(
        _candidate(),
        validator_set,
        previous_hash=genesis_hash,
    )
    prior_hash = str(build_checkpoint_v0(parent_header)["header_hash"])
    header = _header(candidate, validator_set, previous_hash=prior_hash)
    checkpoint = build_checkpoint_v0(header)
    policy = _policy(
        candidate,
        registry,
        header,
        genesis_hash=genesis_hash,
    )
    duty = build_proposer_duty_v0(validator_set=validator_set, height=2)
    proposer = duty["proposer"]
    assert isinstance(proposer, dict)
    assert proposer["validator_id"] == "sequencer-1"

    capability = SpotV7ZenoLedgerCheckpointFinalityAdapterV2(policy).authenticate(
        settlement=_settlement(candidate),
        prior_cursor=ZenoLedgerCheckpointFinalityCursorV1(
            sequence=1,
            checkpoint_hash=prior_hash,
        ),
        header=header,
        replay_observation=_replay_observation(
            candidate,
            header,
            parent_header=parent_header,
        ),
        checkpoint=checkpoint,
        validator_set=validator_set,
        proposer_id=str(proposer["validator_id"]),
        proposer_key_id=str(proposer["key_id"]),
        proposer_envelope=_proposer_envelope(
            str(checkpoint["header_hash"]),
            validator_set,
            height=2,
            proposer_index=1,
        ),
        registry=registry,
        envelopes=_envelopes(str(checkpoint["header_hash"])),
    )

    evidence = json.loads(capability._exact_finality_evidence_bytes)
    assert evidence["proposer_authorship_admission"]["proposer_id"] == "sequencer-1"


def test_non_genesis_finality_requires_parent_state_continuity_observation() -> None:
    candidate = _candidate(epoch_id=2)
    registry = _registry()
    validator_set = _validator_set()
    genesis_hash = _root("checkpoint-genesis")
    prior_hash = _root("unobserved-checkpoint-one")
    header = _header(candidate, validator_set, previous_hash=prior_hash)
    checkpoint = build_checkpoint_v0(header)
    policy = _policy(candidate, registry, header, genesis_hash=genesis_hash)
    proposer = build_proposer_duty_v0(
        validator_set=validator_set,
        height=candidate.epoch_id,
    )["proposer"]
    assert isinstance(proposer, dict)

    with pytest.raises(SpotV7ZenoLedgerFinalityBindingErrorV1) as captured:
        SpotV7ZenoLedgerCheckpointFinalityAdapterV2(policy).authenticate(
            settlement=_settlement(candidate),
            prior_cursor=ZenoLedgerCheckpointFinalityCursorV1(
                sequence=1,
                checkpoint_hash=prior_hash,
            ),
            header=header,
            replay_observation=_replay_observation(candidate, header),
            checkpoint=checkpoint,
            validator_set=validator_set,
            proposer_id=str(proposer["validator_id"]),
            proposer_key_id=str(proposer["key_id"]),
            proposer_envelope=_proposer_envelope(
                str(checkpoint["header_hash"]),
                validator_set,
                height=2,
                proposer_index=1,
            ),
            registry=registry,
            envelopes=_envelopes(str(checkpoint["header_hash"])),
        )

    assert captured.value.code == "replay_parent_state_continuity"


def test_valid_signature_from_unscheduled_validator_cannot_author_header() -> None:
    fixture = _fixture()
    wrong_but_valid = _proposer_envelope(
        str(fixture.checkpoint["header_hash"]),
        fixture.validator_set,
        proposer_index=1,
    )

    with pytest.raises(SpotV7ZenoLedgerFinalityBindingErrorV1) as captured:
        fixture.adapter.authenticate(
            settlement=fixture.settlement,
            prior_cursor=fixture.prior_cursor,
            header=fixture.header,
            replay_observation=fixture.replay_observation,
            checkpoint=fixture.checkpoint,
            validator_set=fixture.validator_set,
            proposer_id=fixture.proposer_id,
            proposer_key_id=fixture.proposer_key_id,
            proposer_envelope=wrong_but_valid,
            registry=fixture.registry,
            envelopes=fixture.envelopes,
        )

    assert captured.value.code == "proposer_authorship"


def test_checkpoint_vote_signature_cannot_be_replayed_as_proposer_authorship() -> None:
    fixture = _fixture()
    scheduled_vote = build_bls_signed_artifact_envelope_v0(
        payload_kind="checkpoint",
        payload_hash=str(fixture.checkpoint["header_hash"]),
        signer_id=fixture.proposer_id,
        key_id=fixture.proposer_key_id,
        private_key_hex=_private_key("sequencer-a"),
    )

    with pytest.raises(SpotV7ZenoLedgerFinalityBindingErrorV1) as captured:
        fixture.adapter.authenticate(
            settlement=fixture.settlement,
            prior_cursor=fixture.prior_cursor,
            header=fixture.header,
            replay_observation=fixture.replay_observation,
            checkpoint=fixture.checkpoint,
            validator_set=fixture.validator_set,
            proposer_id=fixture.proposer_id,
            proposer_key_id=fixture.proposer_key_id,
            proposer_envelope=scheduled_vote,
            registry=fixture.registry,
            envelopes=fixture.envelopes,
        )

    assert captured.value.code == "proposer_authorship"


@pytest.mark.parametrize(
    "untrusted",
    (
        True,
        {"external_finality_verified": True},
        {"ok": True, "status": "accepted"},
        b"caller-authored-finality-report",
        object(),
    ),
)
def test_caller_reports_and_booleans_cannot_enter_finality_adapter(untrusted: object) -> None:
    fixture = _fixture()

    with pytest.raises(TypeError):
        fixture.adapter.authenticate(
            settlement=untrusted,
            prior_cursor=fixture.prior_cursor,
            header=fixture.header,
            replay_observation=fixture.replay_observation,
            checkpoint=fixture.checkpoint,
            validator_set=fixture.validator_set,
            proposer_id=fixture.proposer_id,
            proposer_key_id=fixture.proposer_key_id,
            proposer_envelope=fixture.proposer_envelope,
            registry=fixture.registry,
            envelopes=fixture.envelopes,
        )


@pytest.mark.parametrize(
    "untrusted",
    (
        {"state_replay_checked": True, "receipt_replay_checked": True},
        {"ok": True, "body_bound": True, "config_bound": True},
        b"caller-authored-replay-observation",
        True,
    ),
)
def test_forged_replay_reports_cannot_enter_finality_adapter(untrusted: object) -> None:
    fixture = _fixture()

    with pytest.raises(TypeError, match="private replay-bound observation"):
        fixture.adapter.authenticate(
            settlement=fixture.settlement,
            prior_cursor=fixture.prior_cursor,
            header=fixture.header,
            replay_observation=untrusted,
            checkpoint=fixture.checkpoint,
            validator_set=fixture.validator_set,
            proposer_id=fixture.proposer_id,
            proposer_key_id=fixture.proposer_key_id,
            proposer_envelope=fixture.proposer_envelope,
            registry=fixture.registry,
            envelopes=fixture.envelopes,
        )


def test_invalid_bls_signature_rejects_before_capability_mint(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture()
    malformed = dict(fixture.envelopes[0])
    malformed["signature"] = "0x" + _fixed_bytes("wrong-signature", 96).hex()
    calls = 0
    def record_mint(*_args: object, **_kwargs: object) -> NoReturn:
        nonlocal calls
        calls += 1
        raise AssertionError("finality capability mint reached before signature rejection")

    monkeypatch.setattr(
        adapter_module,
        "_AuthenticatedExactCheckpointFinalityTransitionV2",
        record_mint,
    )
    with pytest.raises(ValueError, match="signature invalid"):
        fixture.adapter.authenticate(
            settlement=fixture.settlement,
            prior_cursor=fixture.prior_cursor,
            header=fixture.header,
            replay_observation=fixture.replay_observation,
            checkpoint=fixture.checkpoint,
            validator_set=fixture.validator_set,
            proposer_id=fixture.proposer_id,
            proposer_key_id=fixture.proposer_key_id,
            proposer_envelope=fixture.proposer_envelope,
            registry=fixture.registry,
            envelopes=(malformed, fixture.envelopes[1]),
        )

    assert calls == 0


def test_registry_must_match_governed_verifier_set_root() -> None:
    fixture = _fixture()
    replacement_registry = _registry(threshold=1)

    with pytest.raises(SpotV7ZenoLedgerFinalityBindingErrorV1) as captured:
        fixture.adapter.authenticate(
            settlement=fixture.settlement,
            prior_cursor=fixture.prior_cursor,
            header=fixture.header,
            replay_observation=fixture.replay_observation,
            checkpoint=fixture.checkpoint,
            validator_set=fixture.validator_set,
            proposer_id=fixture.proposer_id,
            proposer_key_id=fixture.proposer_key_id,
            proposer_envelope=fixture.proposer_envelope,
            registry=replacement_registry,
            envelopes=fixture.envelopes,
        )

    assert captured.value.code == "verifier_set_root"


def test_checkpoint_signer_registry_cannot_replace_canonical_validator_set() -> None:
    fixture = _fixture()
    mutated_header = dict(fixture.header)
    mutated_header["sequencer_set_hash"] = fixture.registry["registry_hash"]
    checkpoint = build_checkpoint_v0(mutated_header)

    with pytest.raises(SpotV7ZenoLedgerFinalityBindingErrorV1) as captured:
        fixture.adapter.authenticate(
            settlement=fixture.settlement,
            prior_cursor=fixture.prior_cursor,
            header=mutated_header,
            replay_observation=fixture.replay_observation,
            checkpoint=checkpoint,
            validator_set=fixture.validator_set,
            proposer_id=fixture.proposer_id,
            proposer_key_id=fixture.proposer_key_id,
            proposer_envelope=_proposer_envelope(
                str(checkpoint["header_hash"]),
                fixture.validator_set,
            ),
            registry=fixture.registry,
            envelopes=_envelopes(str(checkpoint["header_hash"])),
        )

    assert captured.value.code == "scheduled_header_admission"


def test_body_root_substitution_cannot_escape_private_replay_observation() -> None:
    fixture = _fixture()
    mutated_header = dict(fixture.header)
    mutated_header["body_root"] = _root("substituted-body")
    checkpoint = build_checkpoint_v0(mutated_header)

    with pytest.raises(SpotV7ZenoLedgerFinalityBindingErrorV1) as captured:
        fixture.adapter.authenticate(
            settlement=fixture.settlement,
            prior_cursor=fixture.prior_cursor,
            header=mutated_header,
            replay_observation=fixture.replay_observation,
            checkpoint=checkpoint,
            validator_set=fixture.validator_set,
            proposer_id=fixture.proposer_id,
            proposer_key_id=fixture.proposer_key_id,
            proposer_envelope=fixture.proposer_envelope,
            registry=fixture.registry,
            envelopes=fixture.envelopes,
        )

    assert captured.value.code == "replay_body_root"


def test_body_proof_receipt_journal_must_match_candidate_journal() -> None:
    fixture = _fixture()
    candidate = fixture.settlement._candidate_for_atomic_store()
    wrong_journal = _root("body-proof-receipt-wrong-journal")
    header = _header(
        candidate,
        fixture.validator_set,
        previous_hash=fixture.prior_cursor.checkpoint_hash,
        body_proof_journal_hash=wrong_journal,
    )
    checkpoint = build_checkpoint_v0(header)
    replay_observation = _replay_observation(
        candidate,
        header,
        body_proof_journal_hash=wrong_journal,
    )

    with pytest.raises(SpotV7ZenoLedgerFinalityBindingErrorV1) as captured:
        fixture.adapter.authenticate(
            settlement=fixture.settlement,
            prior_cursor=fixture.prior_cursor,
            header=header,
            replay_observation=replay_observation,
            checkpoint=checkpoint,
            validator_set=fixture.validator_set,
            proposer_id=fixture.proposer_id,
            proposer_key_id=fixture.proposer_key_id,
            proposer_envelope=fixture.proposer_envelope,
            registry=fixture.registry,
            envelopes=fixture.envelopes,
        )

    assert captured.value.code == "replay_proof_receipt_journal"


def test_legacy_ledger_validator_set_cannot_replace_scheduled_validator_set() -> None:
    fixture = _fixture()
    legacy_validator_set = {
        "schema": LEDGER_VALIDATOR_SET_SCHEMA_V0,
        "chain_id": CHAIN_ID,
        "epoch": 0,
        "validators": [
            {
                "validator_id": "sequencer-0",
                "public_key": bls_public_key_hex_from_private_key_v0(
                    _private_key("sequencer-a")
                ),
                "voting_power": 1,
            }
        ],
    }

    with pytest.raises(SpotV7ZenoLedgerFinalityBindingErrorV1) as captured:
        fixture.adapter.authenticate(
            settlement=fixture.settlement,
            prior_cursor=fixture.prior_cursor,
            header=fixture.header,
            replay_observation=fixture.replay_observation,
            checkpoint=fixture.checkpoint,
            validator_set=legacy_validator_set,
            proposer_id=fixture.proposer_id,
            proposer_key_id=fixture.proposer_key_id,
            proposer_envelope=fixture.proposer_envelope,
            registry=fixture.registry,
            envelopes=fixture.envelopes,
        )

    assert captured.value.code == "scheduled_header_admission"


@pytest.mark.parametrize(
    ("proposer_id", "proposer_key_id"),
    (
        ("wrong-proposer", "sequencer-bls-0"),
        ("sequencer-0", "wrong-key"),
    ),
)
def test_unscheduled_proposer_identity_rejects_before_quorum(
    proposer_id: str,
    proposer_key_id: str,
) -> None:
    fixture = _fixture()

    with pytest.raises(SpotV7ZenoLedgerFinalityBindingErrorV1) as captured:
        fixture.adapter.authenticate(
            settlement=fixture.settlement,
            prior_cursor=fixture.prior_cursor,
            header=fixture.header,
            replay_observation=fixture.replay_observation,
            checkpoint=fixture.checkpoint,
            validator_set=fixture.validator_set,
            proposer_id=proposer_id,
            proposer_key_id=proposer_key_id,
            proposer_envelope=fixture.proposer_envelope,
            registry=fixture.registry,
            envelopes=fixture.envelopes,
        )

    assert captured.value.code == "scheduled_header_admission"


@pytest.mark.parametrize(
    "mutation",
    ("signature", "signer_id", "key_id", "public_key", "payload_hash"),
)
def test_scheduled_proposer_must_cryptographically_author_header(
    mutation: str,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture()
    malformed = dict(fixture.proposer_envelope)
    replacements = {
        "signature": "0x" + _fixed_bytes("wrong-proposer-signature", 96).hex(),
        "signer_id": "other-sequencer",
        "key_id": "other-sequencer-key",
        "public_key": bls_public_key_hex_from_private_key_v0(_private_key("other-sequencer")),
        "payload_hash": _root("other-proposer-payload"),
    }
    malformed[mutation] = replacements[mutation]
    quorum_calls = 0

    def reject_unexpected_quorum(**_kwargs: object) -> object:
        nonlocal quorum_calls
        quorum_calls += 1
        raise AssertionError("checkpoint quorum must follow proposer authentication")

    monkeypatch.setattr(
        adapter_module,
        "build_live_checkpoint_quorum_admission_v0",
        reject_unexpected_quorum,
    )
    with pytest.raises(SpotV7ZenoLedgerFinalityBindingErrorV1) as captured:
        fixture.adapter.authenticate(
            settlement=fixture.settlement,
            prior_cursor=fixture.prior_cursor,
            header=fixture.header,
            replay_observation=fixture.replay_observation,
            checkpoint=fixture.checkpoint,
            validator_set=fixture.validator_set,
            proposer_id=fixture.proposer_id,
            proposer_key_id=fixture.proposer_key_id,
            proposer_envelope=malformed,
            registry=fixture.registry,
            envelopes=fixture.envelopes,
        )

    assert captured.value.code == "proposer_authorship"
    assert quorum_calls == 0


def test_noncanonical_app_hash_rejects_before_quorum() -> None:
    fixture = _fixture()
    mutated_header = dict(fixture.header)
    mutated_header["app_hash"] = _root("noncanonical-app-hash")
    checkpoint = build_checkpoint_v0(mutated_header)

    with pytest.raises(SpotV7ZenoLedgerFinalityBindingErrorV1) as captured:
        fixture.adapter.authenticate(
            settlement=fixture.settlement,
            prior_cursor=fixture.prior_cursor,
            header=mutated_header,
            replay_observation=fixture.replay_observation,
            checkpoint=checkpoint,
            validator_set=fixture.validator_set,
            proposer_id=fixture.proposer_id,
            proposer_key_id=fixture.proposer_key_id,
            proposer_envelope=_proposer_envelope(
                str(checkpoint["header_hash"]),
                fixture.validator_set,
            ),
            registry=fixture.registry,
            envelopes=_envelopes(str(checkpoint["header_hash"])),
        )

    assert captured.value.code == "app_hash"


def test_deep_input_rejects_before_recursive_json_serialization() -> None:
    fixture = _fixture()
    nested: object = []
    for _ in range(10_000):
        nested = [nested]
    malformed_header = dict(fixture.header)
    malformed_header["untrusted_nested_value"] = nested

    with pytest.raises(ValueError, match="maximum depth"):
        fixture.adapter.authenticate(
            settlement=fixture.settlement,
            prior_cursor=fixture.prior_cursor,
            header=malformed_header,
            replay_observation=fixture.replay_observation,
            checkpoint=fixture.checkpoint,
            validator_set=fixture.validator_set,
            proposer_id=fixture.proposer_id,
            proposer_key_id=fixture.proposer_key_id,
            proposer_envelope=fixture.proposer_envelope,
            registry=fixture.registry,
            envelopes=fixture.envelopes,
        )


def test_wide_input_rejects_before_json_output_allocation() -> None:
    fixture = _fixture()
    malformed_header = dict(fixture.header)
    malformed_header["untrusted_wide_value"] = [None] * 32_769

    with pytest.raises(ValueError, match="item bound"):
        fixture.adapter.authenticate(
            settlement=fixture.settlement,
            prior_cursor=fixture.prior_cursor,
            header=malformed_header,
            replay_observation=fixture.replay_observation,
            checkpoint=fixture.checkpoint,
            validator_set=fixture.validator_set,
            proposer_id=fixture.proposer_id,
            proposer_key_id=fixture.proposer_key_id,
            proposer_envelope=fixture.proposer_envelope,
            registry=fixture.registry,
            envelopes=fixture.envelopes,
        )


def test_escape_amplification_rejects_before_json_output_allocation() -> None:
    fixture = _fixture()
    malformed_header = dict(fixture.header)
    malformed_header["untrusted_escaped_value"] = "\x00" * 200_000

    with pytest.raises(ValueError, match="json size exceeds max_bytes"):
        fixture.adapter.authenticate(
            settlement=fixture.settlement,
            prior_cursor=fixture.prior_cursor,
            header=malformed_header,
            replay_observation=fixture.replay_observation,
            checkpoint=fixture.checkpoint,
            validator_set=fixture.validator_set,
            proposer_id=fixture.proposer_id,
            proposer_key_id=fixture.proposer_key_id,
            proposer_envelope=fixture.proposer_envelope,
            registry=fixture.registry,
            envelopes=fixture.envelopes,
        )


def test_reached_quorum_below_strict_two_thirds_never_mints_finality() -> None:
    candidate = _candidate()
    registry = _registry(threshold=1)
    validator_set = _validator_set()
    genesis_hash = _root("checkpoint-genesis")
    header = _header(candidate, validator_set, previous_hash=genesis_hash)
    checkpoint = build_checkpoint_v0(header)
    policy = _policy(candidate, registry, header, genesis_hash=genesis_hash)
    adapter = SpotV7ZenoLedgerCheckpointFinalityAdapterV2(policy)
    first_envelope = _envelopes(str(checkpoint["header_hash"]))[:1]
    proposer = build_proposer_duty_v0(
        validator_set=validator_set,
        height=candidate.epoch_id,
    )["proposer"]
    assert isinstance(proposer, dict)

    with pytest.raises(SpotV7ZenoLedgerFinalityBindingErrorV1) as captured:
        adapter.authenticate(
            settlement=_settlement(candidate),
            prior_cursor=ZenoLedgerCheckpointFinalityCursorV1(
                sequence=0,
                checkpoint_hash=genesis_hash,
            ),
            header=header,
            replay_observation=_replay_observation(candidate, header),
            checkpoint=checkpoint,
            validator_set=validator_set,
            proposer_id=str(proposer["validator_id"]),
            proposer_key_id=str(proposer["key_id"]),
            proposer_envelope=_proposer_envelope(
                str(checkpoint["header_hash"]),
                validator_set,
            ),
            registry=registry,
            envelopes=first_envelope,
        )

    assert captured.value.code == "quorum_intersection"


@pytest.mark.parametrize(
    ("mutation", "code"),
    (
        ("journal", "proof_journal_hash"),
        ("post_state", "post_state_root"),
        ("parent", "prior_checkpoint_hash"),
        ("sequence", "checkpoint_sequence"),
    ),
)
def test_transition_binding_mutations_reject_before_finality_mint(
    mutation: str,
    code: str,
) -> None:
    fixture = _fixture()
    settlement = fixture.settlement
    cursor = fixture.prior_cursor
    header = fixture.header
    checkpoint = fixture.checkpoint
    envelopes = fixture.envelopes
    proposer_envelope = fixture.proposer_envelope
    if mutation == "journal":
        header = _header(
            settlement._candidate_for_atomic_store(),
            fixture.validator_set,
            previous_hash=cursor.checkpoint_hash,
            proof_journal_hash=_root("wrong-journal"),
        )
        checkpoint = build_checkpoint_v0(header)
        envelopes = _envelopes(str(checkpoint["header_hash"]))
        proposer_envelope = _proposer_envelope(
            str(checkpoint["header_hash"]),
            fixture.validator_set,
        )
    elif mutation == "post_state":
        header = _header(
            settlement._candidate_for_atomic_store(),
            fixture.validator_set,
            previous_hash=cursor.checkpoint_hash,
            post_state_root=_root("wrong-post-state"),
        )
        checkpoint = build_checkpoint_v0(header)
        envelopes = _envelopes(str(checkpoint["header_hash"]))
        proposer_envelope = _proposer_envelope(
            str(checkpoint["header_hash"]),
            fixture.validator_set,
        )
    elif mutation == "parent":
        header = _header(
            settlement._candidate_for_atomic_store(),
            fixture.validator_set,
            previous_hash=_root("wrong-parent"),
        )
        checkpoint = build_checkpoint_v0(header)
        envelopes = _envelopes(str(checkpoint["header_hash"]))
        proposer_envelope = _proposer_envelope(
            str(checkpoint["header_hash"]),
            fixture.validator_set,
        )
    else:
        cursor = replace(cursor, sequence=4)

    with pytest.raises(SpotV7ZenoLedgerFinalityBindingErrorV1) as captured:
        fixture.adapter.authenticate(
            settlement=settlement,
            prior_cursor=cursor,
            header=header,
            replay_observation=fixture.replay_observation,
            checkpoint=checkpoint,
            validator_set=fixture.validator_set,
            proposer_id=fixture.proposer_id,
            proposer_key_id=fixture.proposer_key_id,
            proposer_envelope=proposer_envelope,
            registry=fixture.registry,
            envelopes=envelopes,
        )

    assert captured.value.code == code


def test_governed_config_and_sequencer_policy_are_exact() -> None:
    fixture = _fixture()
    mutated = dict(fixture.header)
    mutated["config_digest"] = _root("other-config")
    mutated["app_hash"] = compute_app_hash_v0(
        {
            "chain_id": mutated["chain_id"],
            "height": mutated["height"],
            "post_state_root": mutated["post_state_root"],
            "evidence_root": mutated["evidence_root"],
            "config_digest": mutated["config_digest"],
            "module_versions_digest": mutated["module_versions_digest"],
        }
    )
    checkpoint = build_checkpoint_v0(mutated)

    with pytest.raises(SpotV7ZenoLedgerFinalityBindingErrorV1) as captured:
        fixture.adapter.authenticate(
            settlement=fixture.settlement,
            prior_cursor=fixture.prior_cursor,
            header=mutated,
            replay_observation=fixture.replay_observation,
            checkpoint=checkpoint,
            validator_set=fixture.validator_set,
            proposer_id=fixture.proposer_id,
            proposer_key_id=fixture.proposer_key_id,
            proposer_envelope=_proposer_envelope(
                str(checkpoint["header_hash"]),
                fixture.validator_set,
            ),
            registry=fixture.registry,
            envelopes=_envelopes(str(checkpoint["header_hash"])),
        )

    assert captured.value.code == "external_finality_policy"


def test_checkpoint_embedded_signature_set_is_forbidden() -> None:
    fixture = _fixture()
    checkpoint = build_checkpoint_v0(
        fixture.header,
        signature_set=[{"accepted": True}],
    )

    with pytest.raises(SpotV7ZenoLedgerFinalityBindingErrorV1) as captured:
        fixture.adapter.authenticate(
            settlement=fixture.settlement,
            prior_cursor=fixture.prior_cursor,
            header=fixture.header,
            replay_observation=fixture.replay_observation,
            checkpoint=checkpoint,
            validator_set=fixture.validator_set,
            proposer_id=fixture.proposer_id,
            proposer_key_id=fixture.proposer_key_id,
            proposer_envelope=fixture.proposer_envelope,
            registry=fixture.registry,
            envelopes=fixture.envelopes,
        )

    assert captured.value.code == "embedded_signature_set"


def test_finality_capability_remains_nontransferable_and_authority_is_conservative() -> None:
    fixture = _fixture()
    capability = _authenticate(fixture)

    assert fixture.adapter.cryptographic_checkpoint_quorum_supported is True
    assert fixture.adapter.release_authority is False
    assert fixture.adapter.settlement_authority is False
    assert fixture.adapter.production_authority is False
    for operation in (copy.copy, copy.deepcopy, pickle.dumps):
        with pytest.raises(TypeError):
            operation(capability)
