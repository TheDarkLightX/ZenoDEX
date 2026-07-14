"""CBC tests for bounded Spot V7 settlement-envelope replay."""

from __future__ import annotations

import copy
import hashlib
import json
import pickle
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Any, cast

import pytest

import src.integration._zrpf_spot_v7_firecracker_authority as firecracker_authority
import src.integration._zrpf_spot_v7_settlement_envelope_contract as replay_contract
from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _candidate_action_ids_root,
    _SpotV7SettlementCandidateInputV1,
)
from src.integration._zrpf_spot_v7_firecracker_authority import (
    _GovernedFirecrackerSpotV7SettlementV1,
)
from src.integration._zrpf_spot_v7_settlement_envelope_replay import (
    SPOT_V7_SETTLEMENT_EFFECT_IDS_ROOT_DOMAIN_V1,
    SpotV7SettlementEnvelopeReplayAdapterV1,
    SpotV7SettlementEnvelopeReplayAdapterV2,
    SpotV7SettlementEnvelopeReplayErrorV1,
    build_spot_v7_settlement_envelope_v1,
    decode_exact_spot_v7_settlement_envelope_v1,
    encode_spot_v7_settlement_envelope_v1,
)
from src.integration._zrpf_spot_v7_zeno_ledger_replay_contract import (
    SPOT_V7_ZENO_LEDGER_BODY_PROOF_RECEIPT_PROJECTION_SCHEMA_V1,
)
from src.integration.dex_engine import DexEngineConfig
from src.integration.dex_snapshot import snapshot_from_state, state_from_snapshot
from src.integration.zeno_ledger_replay import (
    replay_engine_config_digest_v0,
    replay_engine_config_document_v0,
)
from src.integration.zeno_ledger_v0 import (
    BATCH_CUTOFF_SCHEMA_V0,
    BODY_SCHEMA_V0,
    ZERO_ROOT_V0,
    build_header_v0,
    canonical_body_root_v0,
    canonical_header_hash_v0,
    canonical_json_bytes_v0,
    compute_app_hash_v0,
    compute_evidence_root_v0,
    compute_ingress_root_v0,
    compute_tx_root_v0,
    hash_v0,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    SpotV7AssetEffectV1,
    SpotV7CellKindV1,
    SpotV7CellOpeningV1,
    SpotV7CellRoleV1,
    SpotV7CellTransitionV1,
    spot_v7_cell_transitions_root_v1,
)

_ROOT = Path(__file__).resolve().parents[2]
_STATE_FIXTURE = _ROOT / "tests/fixtures/zrpf_spot_state_root_v5_bridge_v1.json"
_SEMANTIC_FIXTURE = _ROOT / "tests/fixtures/zrpf_spot_state_root_v7_semantic_v1.json"
_CHAIN_ID = "zrpf-spot-v7-settlement-replay-test"
_BINDING_DOMAIN = b"zenodex.zrpf.spot_settlement_v7_effect_binding_journal.v1"


def _root(label: str) -> str:
    return hash_v0("zrpf_spot_v7_settlement_replay_test", {"label": label})


def _raw(value: str) -> bytes:
    return bytes.fromhex(value[2:])


def _prefixed_sha256(value: bytes) -> str:
    return "0x" + hashlib.sha256(value).hexdigest()


def _domain_commitment(domain: bytes, value: bytes) -> bytes:
    return hashlib.sha256(len(domain).to_bytes(2, "big") + domain + value).digest()


def _semantic_bytes() -> bytes:
    document = json.loads(_SEMANTIC_FIXTURE.read_text(encoding="utf-8"))
    return bytes.fromhex(document["journal_hex"][2:])


def _state_document() -> dict[str, Any]:
    return json.loads(_STATE_FIXTURE.read_text(encoding="utf-8"))


def _states() -> tuple[object, object]:
    document = _state_document()
    pre = state_from_snapshot(document["pre_state"])
    post = state_from_snapshot(document["post_state"])
    sender = document["sender_pubkey"]
    nonce = document["ingress_nonce"]
    pre.nonces.set_last(sender, nonce - 1)
    post.nonces.set_last(sender, nonce)
    return pre, post


def _transitions(
    action: str,
) -> tuple[tuple[SpotV7CellTransitionV1, ...], tuple[SpotV7AssetEffectV1, ...]]:
    document = _state_document()
    sender = document["sender_pubkey"]
    pool = document["pre_state"]["pools"][0]
    post_pool = document["post_state"]["pools"][0]
    pre_balances = {
        (row["pubkey"], row["asset"]): row["amount"] for row in document["pre_state"]["balances"]
    }
    post_balances = {
        (row["pubkey"], row["asset"]): row["amount"] for row in document["post_state"]["balances"]
    }
    asset0 = pool["asset0"]
    asset1 = pool["asset1"]
    rows = (
        SpotV7CellTransitionV1(
            SpotV7CellRoleV1.DEBIT,
            SpotV7CellOpeningV1(
                SpotV7CellKindV1.ACCOUNT_BALANCE,
                sender,
                asset0,
                pre_balances[(sender, asset0)],
            ),
            SpotV7CellOpeningV1(
                SpotV7CellKindV1.ACCOUNT_BALANCE,
                sender,
                asset0,
                post_balances[(sender, asset0)],
            ),
        ),
        SpotV7CellTransitionV1(
            SpotV7CellRoleV1.CREDIT,
            SpotV7CellOpeningV1(
                SpotV7CellKindV1.ACCOUNT_BALANCE,
                sender,
                asset1,
                pre_balances[(sender, asset1)],
            ),
            SpotV7CellOpeningV1(
                SpotV7CellKindV1.ACCOUNT_BALANCE,
                sender,
                asset1,
                post_balances[(sender, asset1)],
            ),
        ),
        SpotV7CellTransitionV1(
            SpotV7CellRoleV1.CREDIT,
            SpotV7CellOpeningV1(
                SpotV7CellKindV1.POOL_RESERVE,
                pool["pool_id"],
                asset0,
                pool["reserve0"],
            ),
            SpotV7CellOpeningV1(
                SpotV7CellKindV1.POOL_RESERVE,
                pool["pool_id"],
                asset0,
                post_pool["reserve0"],
            ),
        ),
        SpotV7CellTransitionV1(
            SpotV7CellRoleV1.DEBIT,
            SpotV7CellOpeningV1(
                SpotV7CellKindV1.POOL_RESERVE,
                pool["pool_id"],
                asset1,
                pool["reserve1"],
            ),
            SpotV7CellOpeningV1(
                SpotV7CellKindV1.POOL_RESERVE,
                pool["pool_id"],
                asset1,
                post_pool["reserve1"],
            ),
        ),
    )
    ordered = tuple(sorted(rows, key=lambda row: row.cell_key))
    effects = tuple(
        sorted(
            (
                SpotV7AssetEffectV1(action, asset0, 1_000),
                SpotV7AssetEffectV1(action, asset1, 1_992),
            ),
            key=lambda row: (row.asset_id, row.effect_id),
        )
    )
    return ordered, effects


def _v7_journal(candidate: _SpotV7SettlementCandidateInputV1) -> bytes:
    semantic = _semantic_bytes()
    plan = candidate.exact_plan_b_bytes
    binding_fields = (
        semantic[2:34],
        semantic[34:66],
        _raw(_root("source-journal")),
        _raw(_root("source-plan")),
        _raw(candidate.settlement_effect_plan_commitment),
        _raw(candidate.cell_transitions_root),
        _raw(candidate.pre_state_root),
        _raw(candidate.post_state_root),
        _raw(candidate.economic_action_id),
        _raw(_root("action-semantics")),
        _raw(_root("effect-commitment")),
        _raw(_root("public-policy")),
    )
    binding = (1).to_bytes(2, "big") + b"".join(binding_fields)
    journal_fields = (
        _raw(_root("source-child-program")),
        _raw(_root("source-child-profile")),
        _raw(candidate.source_child_claim_binding),
        _raw(candidate.source_child_journal_sha256),
        _raw(candidate.data_availability_certificate_root),
        _raw(candidate.data_root),
        _raw(_root("source-replay")),
        _raw(_root("host-input")),
        hashlib.sha256(semantic).digest(),
        _domain_commitment(_BINDING_DOMAIN, binding),
        _raw(candidate.settlement_effect_plan_commitment),
        hashlib.sha256(plan).digest(),
        _raw(_candidate_action_ids_root(candidate)),
    )
    header_bytes = 8 + 2 + 4 + 4 + 2 + 2 + 4
    total = header_bytes + 13 * 32 + len(semantic) + len(binding) + len(plan)
    return b"".join(
        (
            b"ZSPTV7J1",
            (1).to_bytes(2, "big"),
            total.to_bytes(4, "big"),
            (538).to_bytes(4, "big"),
            len(semantic).to_bytes(2, "big"),
            len(binding).to_bytes(2, "big"),
            len(plan).to_bytes(4, "big"),
            b"".join(journal_fields),
            semantic,
            binding,
            plan,
        )
    )


def _candidate() -> _SpotV7SettlementCandidateInputV1:
    document = _state_document()
    expected = document["expected"]
    action = _root("action")
    transitions, effects = _transitions(action)
    partial = _SpotV7SettlementCandidateInputV1(
        application_id=_root("application"),
        chain_or_domain_id=_root("domain"),
        epoch_id=1,
        verified_program_id=_root("program"),
        verified_profile_id=_root("profile"),
        verified_program_manifest_root=_root("manifest"),
        source_child_claim_binding=_root("child-claim"),
        source_child_journal_sha256=_root("child-journal"),
        data_availability_certificate_root=_root("da-certificate"),
        data_root=_root("data"),
        settlement_effect_plan_commitment=_root("plan"),
        pre_state_root=expected["pre_state_root_v5"],
        post_state_root=expected["post_state_root_v5"],
        economic_action_id=action,
        authorization_nullifier=_root("authorization"),
        authorization_grant_spend_nullifier=_root("grant-spend"),
        consumed_object_ids=(_root("consumed"),),
        cell_transitions=transitions,
        cell_transitions_root=spot_v7_cell_transitions_root_v1(transitions),
        asset_effects=effects,
        exact_v7_receipt_bytes=b"exact-v7-receipt",
        exact_v7_journal_bytes=b"placeholder",
        exact_plan_b_bytes=b"exact-v7-plan-b",
        exact_firecracker_execution_record_bytes=b"exact-firecracker-record",
        exact_firecracker_output_bytes=b"exact-firecracker-output",
    )
    return replace(partial, exact_v7_journal_bytes=_v7_journal(partial))


def _settlement(
    candidate: _SpotV7SettlementCandidateInputV1,
) -> _GovernedFirecrackerSpotV7SettlementV1:
    capability = object.__new__(_GovernedFirecrackerSpotV7SettlementV1)
    object.__setattr__(capability, "_candidate", candidate)
    object.__setattr__(capability, "_runtime_execution", object())
    object.__setattr__(
        capability,
        "_seal",
        firecracker_authority._GOVERNED_BINDER_SEAL_V1,
    )
    return capability


def _body(candidate: _SpotV7SettlementCandidateInputV1, envelope: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema": BODY_SCHEMA_V0,
        "chain_id": _CHAIN_ID,
        "height": candidate.epoch_id,
        "ingress": {
            "batch_cutoff": {
                "schema": BATCH_CUTOFF_SCHEMA_V0,
                "chain_id": _CHAIN_ID,
                "height": candidate.epoch_id,
                "cutoff_time_ms": 1_784_000_000_000,
                "cutoff_sequence": candidate.epoch_id,
                "sequencer_id": "sequencer-0",
                "policy_id": "spot-v7-settlement-envelope-replay-v1",
                "policy_digest": _root("ingress-policy"),
            },
            "ingress_receipts": [],
            "forced_inclusion_requests": [],
            "forced_inclusion_decisions": [],
        },
        "transactions": [],
        "settlement_envelopes": [envelope],
        "evidence": {
            "upba_certificates": [],
            "price_grid_tables": [],
            "uniform_batch_hypergraph_roots": [],
            "oracle_packets": [],
            "proof_receipts": [
                {
                    "schema": SPOT_V7_ZENO_LEDGER_BODY_PROOF_RECEIPT_PROJECTION_SCHEMA_V1,
                    "proof_journal_hash": _prefixed_sha256(candidate.exact_v7_journal_bytes),
                }
            ],
            "rejection_receipts": [],
        },
    }


def _header(
    candidate: _SpotV7SettlementCandidateInputV1,
    body: dict[str, Any],
    config_document: dict[str, Any],
) -> dict[str, Any]:
    evidence_root = compute_evidence_root_v0(body["evidence"])
    config_digest = replay_engine_config_digest_v0(config_document)
    app_hash = compute_app_hash_v0(
        {
            "chain_id": _CHAIN_ID,
            "height": candidate.epoch_id,
            "post_state_root": candidate.post_state_root,
            "evidence_root": evidence_root,
            "config_digest": config_digest,
            "module_versions_digest": _root("modules"),
        }
    )
    return build_header_v0(
        chain_id=_CHAIN_ID,
        height=candidate.epoch_id,
        time_ms=1_784_000_000_001,
        prev_header_hash=ZERO_ROOT_V0,
        sequencer_set_hash=_root("sequencers"),
        ingress_root=compute_ingress_root_v0(body["ingress"]),
        tx_root=compute_tx_root_v0(body["transactions"]),
        pre_state_root=candidate.pre_state_root,
        post_state_root=candidate.post_state_root,
        app_hash=app_hash,
        evidence_root=evidence_root,
        body_root=canonical_body_root_v0(body),
        data_availability_root=candidate.data_root,
        proof_journal_hash=_prefixed_sha256(candidate.exact_v7_journal_bytes),
        config_digest=config_digest,
        module_versions_digest=_root("modules"),
        signature_set_root=ZERO_ROOT_V0,
    )


@dataclass(frozen=True)
class _Fixture:
    adapter: SpotV7SettlementEnvelopeReplayAdapterV1
    settlement: _GovernedFirecrackerSpotV7SettlementV1
    candidate: _SpotV7SettlementCandidateInputV1
    pre_snapshot: dict[str, Any]
    envelope: dict[str, Any]
    body: dict[str, Any]
    header: dict[str, Any]


def _fixture() -> _Fixture:
    candidate = _candidate()
    settlement = _settlement(candidate)
    config_document = replay_engine_config_document_v0(DexEngineConfig(chain_id=_CHAIN_ID))
    envelope = build_spot_v7_settlement_envelope_v1(settlement)
    body = _body(candidate, envelope)
    pre_state, _post_state = _states()
    return _Fixture(
        adapter=SpotV7SettlementEnvelopeReplayAdapterV1(config_document),
        settlement=settlement,
        candidate=candidate,
        pre_snapshot=snapshot_from_state(pre_state).data,
        envelope=envelope,
        body=body,
        header=_header(candidate, body, config_document),
    )


def test_exact_envelope_codec_round_trips_and_rejects_noncanonical_bytes() -> None:
    fixture = _fixture()
    encoded = encode_spot_v7_settlement_envelope_v1(fixture.envelope)

    assert decode_exact_spot_v7_settlement_envelope_v1(encoded) == fixture.envelope
    with pytest.raises(SpotV7SettlementEnvelopeReplayErrorV1) as captured:
        decode_exact_spot_v7_settlement_envelope_v1(b" " + encoded)

    assert captured.value.code == "canonical_envelope"


def test_exact_envelope_codec_rejects_duplicate_keys() -> None:
    with pytest.raises(SpotV7SettlementEnvelopeReplayErrorV1) as captured:
        decode_exact_spot_v7_settlement_envelope_v1(b'{"schema":"a","schema":"b"}')

    assert captured.value.code == "canonical_envelope"


@pytest.mark.parametrize(
    "unsupported_value",
    (
        (_root("tuple-value"),),
        1 << 1_000_000,
    ),
    ids=("nested_tuple", "oversized_integer"),
)
def test_envelope_snapshot_failures_have_one_stable_reject_boundary(
    unsupported_value: object,
) -> None:
    fixture = _fixture()
    envelope = copy.deepcopy(fixture.envelope)
    envelope["proposal"]["epoch_id"] = unsupported_value

    with pytest.raises(SpotV7SettlementEnvelopeReplayErrorV1) as captured:
        encode_spot_v7_settlement_envelope_v1(envelope)

    assert captured.value.code == "envelope_size"


def test_replay_evaluation_is_deterministic_for_acceptance_and_rejection() -> None:
    fixture = _fixture()
    accepted_a = fixture.adapter.evaluate(
        settlement=fixture.settlement,
        envelope=fixture.envelope,
        pre_snapshot=fixture.pre_snapshot,
    )
    accepted_b = fixture.adapter.evaluate(
        settlement=fixture.settlement,
        envelope=copy.deepcopy(fixture.envelope),
        pre_snapshot=copy.deepcopy(fixture.pre_snapshot),
    )
    mutated = copy.deepcopy(fixture.envelope)
    mutated["proposal"]["settlement_effect_plan_commitment"] = _root("wrong-plan")
    rejected_a = fixture.adapter.evaluate(
        settlement=fixture.settlement,
        envelope=mutated,
        pre_snapshot=fixture.pre_snapshot,
    )
    rejected_b = fixture.adapter.evaluate(
        settlement=fixture.settlement,
        envelope=copy.deepcopy(mutated),
        pre_snapshot=copy.deepcopy(fixture.pre_snapshot),
    )

    assert accepted_a == accepted_b == fixture.envelope["expected_receipt"]
    assert accepted_a["accepted"] is True
    assert rejected_a == rejected_b
    assert rejected_a["accepted"] is False
    assert rejected_a["reject_code"] == "candidate_binding"
    assert rejected_a["state_changed"] is False


def test_authenticated_replay_binds_exact_plan_openings_state_and_candidate() -> None:
    fixture = _fixture()

    observation = fixture.adapter.authenticate(
        settlement=fixture.settlement,
        header=fixture.header,
        body=fixture.body,
        pre_snapshot=fixture.pre_snapshot,
    )

    projection = observation._projection_for_finality_adapter()
    assert projection.pre_state_root == fixture.candidate.pre_state_root
    assert projection.post_state_root == fixture.candidate.post_state_root
    assert projection.settlement_effect_plan_commitment == (
        fixture.candidate.settlement_effect_plan_commitment
    )
    assert projection.cell_transitions_root == fixture.candidate.cell_transitions_root
    assert projection.economic_action_id == fixture.candidate.economic_action_id
    assert projection.receipt_accepted is True
    assert observation.settlement_authority is False
    assert observation.release_authority is False
    assert observation.production_authority is False


@pytest.mark.parametrize(
    ("path", "replacement", "expected_code"),
    (
        (
            ("proposal", "settlement_effect_plan_commitment"),
            _root("wrong-plan"),
            "candidate_binding",
        ),
        (("proposal", "pre_state_root"), _root("wrong-pre"), "candidate_binding"),
        (("proposal", "post_state_root"), _root("wrong-post"), "candidate_binding"),
        (("proposal", "economic_action_id"), _root("wrong-action"), "candidate_binding"),
        (("proposal", "authorization_nullifier"), _root("wrong-nullifier"), "candidate_binding"),
        (("proposal", "sender_pubkey"), "0x" + "bb" * 48, "candidate_binding"),
        (("proposal", "epoch_id"), True, "candidate_binding"),
        (("proposal", "ingress_nonce"), 8, "candidate_binding"),
        (("proposal", "cell_transitions", 0, "post", "atoms"), 2_093, "candidate_binding"),
        (("proposal", "asset_effects", 0, "amount_atoms"), 999, "candidate_binding"),
        (("expected_receipt", "economic_action_id"), _root("wrong-receipt"), "committed_receipt"),
        (("expected_receipt", "accepted"), 1, "committed_receipt"),
        (("expected_receipt", "state_changed"), 1, "committed_receipt"),
    ),
)
def test_candidate_field_substitutions_fail_closed(
    path: tuple[object, ...], replacement: object, expected_code: str
) -> None:
    fixture = _fixture()
    body = copy.deepcopy(fixture.body)
    cursor: Any = body["settlement_envelopes"][0]
    for component in path[:-1]:
        cursor = cursor[component]
    cursor[path[-1]] = replacement
    config_document = replay_engine_config_document_v0(DexEngineConfig(chain_id=_CHAIN_ID))
    header = _header(fixture.candidate, body, config_document)

    with pytest.raises(SpotV7SettlementEnvelopeReplayErrorV1) as captured:
        fixture.adapter.authenticate(
            settlement=fixture.settlement,
            header=header,
            body=body,
            pre_snapshot=fixture.pre_snapshot,
        )

    assert captured.value.code == expected_code


def test_repaired_committed_rejection_cannot_mint_authenticated_observation() -> None:
    fixture = _fixture()
    body = copy.deepcopy(fixture.body)
    envelope = body["settlement_envelopes"][0]
    envelope["proposal"]["settlement_effect_plan_commitment"] = _root("wrong-plan")
    envelope["expected_receipt"] = fixture.adapter.evaluate(
        settlement=fixture.settlement,
        envelope=envelope,
        pre_snapshot=fixture.pre_snapshot,
    )
    config_document = replay_engine_config_document_v0(DexEngineConfig(chain_id=_CHAIN_ID))
    header = _header(fixture.candidate, body, config_document)

    with pytest.raises(SpotV7SettlementEnvelopeReplayErrorV1) as captured:
        fixture.adapter.authenticate(
            settlement=fixture.settlement,
            header=header,
            body=body,
            pre_snapshot=fixture.pre_snapshot,
        )

    assert captured.value.code == "settlement_rejected"


def test_bool_integer_alias_cannot_repair_receipt_and_mint_observation() -> None:
    fixture = _fixture()
    body = copy.deepcopy(fixture.body)
    envelope = body["settlement_envelopes"][0]
    assert envelope["proposal"]["epoch_id"] == 1
    envelope["proposal"]["epoch_id"] = True
    envelope["expected_receipt"] = fixture.adapter.evaluate(
        settlement=fixture.settlement,
        envelope=envelope,
        pre_snapshot=fixture.pre_snapshot,
    )
    config_document = replay_engine_config_document_v0(DexEngineConfig(chain_id=_CHAIN_ID))
    header = _header(fixture.candidate, body, config_document)

    with pytest.raises(SpotV7SettlementEnvelopeReplayErrorV1) as captured:
        fixture.adapter.authenticate(
            settlement=fixture.settlement,
            header=header,
            body=body,
            pre_snapshot=fixture.pre_snapshot,
        )

    assert captured.value.code == "settlement_rejected"


def test_pre_state_opening_substitution_rejects_without_state_authority() -> None:
    fixture = _fixture()
    snapshot = copy.deepcopy(fixture.pre_snapshot)
    snapshot["balances"][0]["amount"] += 1

    receipt = fixture.adapter.evaluate(
        settlement=fixture.settlement,
        envelope=fixture.envelope,
        pre_snapshot=snapshot,
    )

    assert receipt["accepted"] is False
    assert receipt["reject_code"] == "pre_state_root"
    assert receipt["state_changed"] is False


def test_header_and_body_must_commit_the_exact_candidate_transition() -> None:
    fixture = _fixture()
    wrong_header = {**fixture.header, "post_state_root": _root("wrong-header-post")}

    with pytest.raises(SpotV7SettlementEnvelopeReplayErrorV1) as captured:
        fixture.adapter.authenticate(
            settlement=fixture.settlement,
            header=wrong_header,
            body=fixture.body,
            pre_snapshot=fixture.pre_snapshot,
        )

    assert captured.value.code == "header_body_binding"


def test_engine_config_chain_must_match_the_committed_ledger_chain() -> None:
    fixture = _fixture()
    other_config = replay_engine_config_document_v0(DexEngineConfig(chain_id="other-chain"))
    adapter = SpotV7SettlementEnvelopeReplayAdapterV1(other_config)
    header = _header(fixture.candidate, fixture.body, other_config)

    with pytest.raises(SpotV7SettlementEnvelopeReplayErrorV1) as captured:
        adapter.authenticate(
            settlement=fixture.settlement,
            header=header,
            body=fixture.body,
            pre_snapshot=fixture.pre_snapshot,
        )

    assert captured.value.code == "config_chain_id"


def test_parent_state_match_without_hash_linkage_cannot_authorize_replay() -> None:
    fixture = _fixture()
    parent = {
        **fixture.header,
        "height": fixture.header["height"] - 1,
        "post_state_root": fixture.candidate.pre_state_root,
    }
    assert fixture.header["prev_header_hash"] != canonical_header_hash_v0(parent)

    with pytest.raises(SpotV7SettlementEnvelopeReplayErrorV1) as captured:
        fixture.adapter.authenticate(
            settlement=fixture.settlement,
            header=fixture.header,
            body=fixture.body,
            pre_snapshot=fixture.pre_snapshot,
            parent_header=parent,
        )

    assert captured.value.code == "header_body_binding"


def test_linked_parent_with_exact_state_continuity_is_accepted() -> None:
    fixture = _fixture()
    parent = {
        **fixture.header,
        "height": 0,
        "post_state_root": fixture.candidate.pre_state_root,
    }
    child = {
        **fixture.header,
        "prev_header_hash": canonical_header_hash_v0(parent),
    }

    observation = fixture.adapter.authenticate(
        settlement=fixture.settlement,
        header=child,
        body=fixture.body,
        pre_snapshot=fixture.pre_snapshot,
        parent_header=parent,
    )

    assert observation._projection_for_finality_adapter().parent_header_hash == (
        canonical_header_hash_v0(parent)
    )


def test_noninitial_header_requires_an_exact_parent_anchor() -> None:
    fixture = _fixture()
    candidate = replace(fixture.candidate, epoch_id=2)
    settlement = _settlement(candidate)
    envelope = build_spot_v7_settlement_envelope_v1(settlement)
    body = _body(candidate, envelope)
    config = replay_engine_config_document_v0(DexEngineConfig(chain_id=_CHAIN_ID))
    header = _header(candidate, body, config)

    with pytest.raises(SpotV7SettlementEnvelopeReplayErrorV1) as captured:
        fixture.adapter.authenticate(
            settlement=settlement,
            header=header,
            body=body,
            pre_snapshot=fixture.pre_snapshot,
        )

    assert captured.value.code == "parent_anchor"


def test_nested_semantic_and_effect_binding_state_substitution_rejects() -> None:
    fixture = _fixture()
    journal = bytearray(fixture.candidate.exact_v7_journal_bytes)
    journal_header_bytes = 26
    fixed_fields_bytes = 13 * 32
    semantic_offset = journal_header_bytes + fixed_fields_bytes
    semantic_pre_state_offset = semantic_offset + 2 + 6 * 32
    journal[semantic_pre_state_offset] ^= 1
    semantic = bytes(journal[semantic_offset : semantic_offset + 310])
    semantic_hash_offset = journal_header_bytes + 8 * 32
    journal[semantic_hash_offset : semantic_hash_offset + 32] = hashlib.sha256(semantic).digest()
    candidate = replace(
        fixture.candidate,
        exact_v7_journal_bytes=bytes(journal),
    )

    with pytest.raises(SpotV7SettlementEnvelopeReplayErrorV1) as captured:
        build_spot_v7_settlement_envelope_v1(_settlement(candidate))

    assert captured.value.code == "candidate_journal"


@pytest.mark.parametrize("profile_field_index", (0, 1))
def test_nested_semantic_and_binding_profile_substitution_rejects(
    profile_field_index: int,
) -> None:
    fixture = _fixture()
    journal = bytearray(fixture.candidate.exact_v7_journal_bytes)
    journal_header_bytes = 26
    semantic_bytes = 310
    semantic_offset = journal_header_bytes + 13 * 32
    binding_offset = semantic_offset + semantic_bytes
    semantic_field_offset = semantic_offset + 2 + profile_field_index * 32
    binding_field_offset = binding_offset + 2 + profile_field_index * 32
    journal[semantic_field_offset] ^= 1
    journal[binding_field_offset] ^= 1
    semantic = bytes(journal[semantic_offset : semantic_offset + semantic_bytes])
    binding = bytes(journal[binding_offset : binding_offset + 386])
    semantic_hash_offset = journal_header_bytes + 8 * 32
    binding_hash_offset = journal_header_bytes + 9 * 32
    journal[semantic_hash_offset : semantic_hash_offset + 32] = hashlib.sha256(semantic).digest()
    journal[binding_hash_offset : binding_hash_offset + 32] = _domain_commitment(
        _BINDING_DOMAIN,
        binding,
    )
    candidate = replace(fixture.candidate, exact_v7_journal_bytes=bytes(journal))

    with pytest.raises(SpotV7SettlementEnvelopeReplayErrorV1) as captured:
        build_spot_v7_settlement_envelope_v1(_settlement(candidate))

    assert captured.value.code == "candidate_journal"


def test_exact_plan_bytes_substitution_rejects_before_envelope_construction() -> None:
    fixture = _fixture()
    candidate = replace(
        fixture.candidate,
        exact_plan_b_bytes=fixture.candidate.exact_plan_b_bytes + b"-substitution",
    )

    with pytest.raises(SpotV7SettlementEnvelopeReplayErrorV1) as captured:
        build_spot_v7_settlement_envelope_v1(_settlement(candidate))

    assert captured.value.code == "candidate_journal"


def test_journal_nonce_mismatch_rejects_during_state_replay() -> None:
    fixture = _fixture()
    journal = bytearray(fixture.candidate.exact_v7_journal_bytes)
    journal_header_bytes = 26
    semantic_offset = journal_header_bytes + 13 * 32
    semantic_nonce_offset = semantic_offset + 2 + 8 * 32 + 48
    journal[semantic_nonce_offset : semantic_nonce_offset + 4] = (8).to_bytes(4, "big")
    semantic = bytes(journal[semantic_offset : semantic_offset + 310])
    semantic_hash_offset = journal_header_bytes + 8 * 32
    journal[semantic_hash_offset : semantic_hash_offset + 32] = hashlib.sha256(semantic).digest()
    candidate = replace(fixture.candidate, exact_v7_journal_bytes=bytes(journal))
    settlement = _settlement(candidate)
    envelope = build_spot_v7_settlement_envelope_v1(settlement)

    receipt = fixture.adapter.evaluate(
        settlement=settlement,
        envelope=envelope,
        pre_snapshot=fixture.pre_snapshot,
    )

    assert receipt["accepted"] is False
    assert receipt["reject_code"] == "nonce_transition"


def test_journal_sender_must_own_both_account_cell_transitions() -> None:
    fixture = _fixture()
    other_sender = "0x" + "bb" * 48
    substituted: list[SpotV7CellTransitionV1] = []
    for row in fixture.candidate.cell_transitions:
        if row.pre.kind is SpotV7CellKindV1.ACCOUNT_BALANCE:
            substituted.append(
                SpotV7CellTransitionV1(
                    row.role,
                    replace(row.pre, subject_id=other_sender),
                    replace(row.post, subject_id=other_sender),
                )
            )
        else:
            substituted.append(row)
    transitions = tuple(sorted(substituted, key=lambda row: row.cell_key))
    partial = replace(
        fixture.candidate,
        cell_transitions=transitions,
        cell_transitions_root=spot_v7_cell_transitions_root_v1(transitions),
    )
    candidate = replace(partial, exact_v7_journal_bytes=_v7_journal(partial))
    settlement = _settlement(candidate)
    envelope = build_spot_v7_settlement_envelope_v1(settlement)

    receipt = fixture.adapter.evaluate(
        settlement=settlement,
        envelope=envelope,
        pre_snapshot=fixture.pre_snapshot,
    )

    assert receipt["accepted"] is False
    assert receipt["reject_code"] == "sender_transition"


def test_plain_candidate_or_plain_envelope_cannot_substitute_for_sealed_candidate() -> None:
    fixture = _fixture()

    with pytest.raises(TypeError):
        fixture.adapter.authenticate(
            settlement=fixture.candidate,
            header=fixture.header,
            body=fixture.body,
            pre_snapshot=fixture.pre_snapshot,
        )


def test_profile_remains_authority_false() -> None:
    fixture = _fixture()

    assert fixture.adapter.proof_receipt_authentication_established is False
    assert fixture.adapter.application_domain_to_ledger_chain_binding_established is False
    assert fixture.adapter.settlement_authority is False
    assert fixture.adapter.release_authority is False
    assert fixture.adapter.production_authority is False


def test_bounded_depth_two_envelope_mutation_frontier_fails_closed() -> None:
    """Offline discovery guardrail; this is not a correctness proof."""

    fixture = _fixture()
    mutations = (
        (("proposal", "settlement_effect_plan_commitment"), _root("atlas-plan")),
        (("proposal", "ingress_nonce"), 8),
        (("proposal", "cell_transitions", 0, "post", "atoms"), 2_093),
        (("expected_receipt", "economic_action_id"), _root("atlas-receipt")),
    )
    observed_codes: set[str] = set()
    explored = 0
    for first_index, first in enumerate(mutations):
        for second_index in range(-1, len(mutations)):
            if second_index == first_index:
                continue
            body = copy.deepcopy(fixture.body)
            for path, value in (first,) if second_index < 0 else (first, mutations[second_index]):
                cursor: Any = body["settlement_envelopes"][0]
                for component in path[:-1]:
                    cursor = cursor[component]
                cursor[path[-1]] = value
            config = replay_engine_config_document_v0(DexEngineConfig(chain_id=_CHAIN_ID))
            header = _header(fixture.candidate, body, config)
            with pytest.raises(SpotV7SettlementEnvelopeReplayErrorV1) as captured:
                fixture.adapter.authenticate(
                    settlement=fixture.settlement,
                    header=header,
                    body=body,
                    pre_snapshot=fixture.pre_snapshot,
                )
            observed_codes.add(captured.value.code)
            explored += 1

    assert explored == 16
    assert observed_codes == {"candidate_binding", "committed_receipt"}


def _v2_observation() -> tuple[
    _Fixture,
    replay_contract._AuthenticatedSpotV7SettlementReplayObservationV2,
]:
    fixture = _fixture()
    config = replay_engine_config_document_v0(DexEngineConfig(chain_id=_CHAIN_ID))
    observation = SpotV7SettlementEnvelopeReplayAdapterV2(config).authenticate(
        settlement=fixture.settlement,
        header=fixture.header,
        body=fixture.body,
        pre_snapshot=fixture.pre_snapshot,
    )
    return fixture, observation


def _v2_persisted_inputs(
    observation: replay_contract._AuthenticatedSpotV7SettlementReplayObservationV2,
) -> Any:
    return observation._durable_replay_packet_for_history_reverification()._persisted_inputs_for_storage()


def test_v2_retains_exact_canonical_replay_material_with_scoped_claims() -> None:
    fixture, observation = _v2_observation()

    projection = observation._projection_for_finality_adapter()
    material = observation._exact_replay_material_for_history_reverification()
    persisted = _v2_persisted_inputs(observation)
    config = replay_engine_config_document_v0(DexEngineConfig(chain_id=_CHAIN_ID))

    assert material.exact_config_document_bytes == canonical_json_bytes_v0(config)
    assert material.exact_pre_state_snapshot_bytes == canonical_json_bytes_v0(fixture.pre_snapshot)
    assert material.exact_config_document_bytes == persisted.exact_config_document_bytes
    assert material.exact_pre_state_snapshot_bytes == persisted.exact_pre_state_snapshot_bytes
    assert projection.config_document_sha256 == _prefixed_sha256(
        material.exact_config_document_bytes
    )
    assert projection.pre_state_snapshot_sha256 == _prefixed_sha256(
        material.exact_pre_state_snapshot_bytes
    )
    assert observation._header_for_finality_adapter() == fixture.header
    assert (
        observation._canonical_projection_for_finality_adapter()["replay_material_root"]
        == projection.replay_material_root
    )
    assert projection.asset_effect_ids_root == hash_v0(
        SPOT_V7_SETTLEMENT_EFFECT_IDS_ROOT_DOMAIN_V1,
        {"effect_ids": [row.effect_id for row in fixture.candidate.asset_effects]},
    )
    assert observation.exact_replay_material_authenticated is True
    assert observation.durable_settlement_replay_reverification_material_retained is True
    assert observation.durable_settlement_replay_reverified is False
    assert observation.application_domain_to_ledger_chain_binding_established is False
    assert observation.settlement_authority is False
    assert observation.release_authority is False
    assert observation.production_authority is False


@pytest.mark.parametrize(
    "artifact_name",
    ("config", "pre_state"),
)
def test_v2_constructor_rejects_config_and_pre_state_substitution(
    artifact_name: str,
) -> None:
    _fixture_value, observation = _v2_observation()
    projection = observation._projection_for_finality_adapter()
    persisted = _v2_persisted_inputs(observation)
    config_bytes = persisted.exact_config_document_bytes
    pre_state_bytes = persisted.exact_pre_state_snapshot_bytes
    if artifact_name == "config":
        config = json.loads(config_bytes)
        config["config"]["max_intents"] += 1
        config_bytes = canonical_json_bytes_v0(config)
    else:
        pre_state = json.loads(pre_state_bytes)
        pre_state["balances"].reverse()
        pre_state_bytes = canonical_json_bytes_v0(pre_state)

    with pytest.raises(ValueError):
        replay_contract._AuthenticatedSpotV7SettlementReplayObservationV2(
            projection,
            exact_header_bytes=persisted.exact_header_bytes,
            exact_body_bytes=persisted.exact_body_bytes,
            exact_envelope_bytes=persisted.exact_envelope_bytes,
            exact_receipt_bytes=persisted.exact_receipt_bytes,
            exact_evidence_bytes=persisted.exact_evidence_bytes,
            exact_config_document_bytes=config_bytes,
            exact_pre_state_snapshot_bytes=pre_state_bytes,
            seal=replay_contract._SETTLEMENT_REPLAY_OBSERVATION_SEAL_V2,
        )


@pytest.mark.parametrize("artifact_name", ("config", "pre_state"))
def test_v2_constructor_rejects_noncanonical_retained_replay_material(
    artifact_name: str,
) -> None:
    _fixture_value, observation = _v2_observation()
    projection = observation._projection_for_finality_adapter()
    persisted = _v2_persisted_inputs(observation)
    config_bytes = persisted.exact_config_document_bytes
    pre_state_bytes = persisted.exact_pre_state_snapshot_bytes
    if artifact_name == "config":
        config_bytes = b" " + config_bytes
        config_sha256 = _prefixed_sha256(config_bytes)
        pre_state_sha256 = projection.pre_state_snapshot_sha256
    else:
        pre_state_bytes = b" " + pre_state_bytes
        config_sha256 = projection.config_document_sha256
        pre_state_sha256 = _prefixed_sha256(pre_state_bytes)
    material_root = replay_contract._derive_replay_material_root_v2(
        chain_id=projection.chain_id,
        height=projection.height,
        candidate_settlement_commitment=projection.candidate_settlement_commitment,
        envelope_sha256=projection.envelope_sha256,
        config_digest=projection.config_digest,
        config_document_sha256=config_sha256,
        pre_state_root=projection.pre_state_root,
        pre_state_snapshot_sha256=pre_state_sha256,
    )
    evidence = json.loads(persisted.exact_evidence_bytes)
    evidence["config_document_sha256"] = config_sha256
    evidence["pre_state_snapshot_sha256"] = pre_state_sha256
    evidence["replay_material_root"] = material_root
    evidence_bytes = canonical_json_bytes_v0(evidence)
    substituted_projection = replace(
        projection,
        config_document_sha256=config_sha256,
        pre_state_snapshot_sha256=pre_state_sha256,
        replay_material_root=material_root,
        observation_evidence_root=_prefixed_sha256(evidence_bytes),
    )

    with pytest.raises(ValueError, match="exact canonical JSON object"):
        replay_contract._AuthenticatedSpotV7SettlementReplayObservationV2(
            substituted_projection,
            exact_header_bytes=persisted.exact_header_bytes,
            exact_body_bytes=persisted.exact_body_bytes,
            exact_envelope_bytes=persisted.exact_envelope_bytes,
            exact_receipt_bytes=persisted.exact_receipt_bytes,
            exact_evidence_bytes=evidence_bytes,
            exact_config_document_bytes=config_bytes,
            exact_pre_state_snapshot_bytes=pre_state_bytes,
            seal=replay_contract._SETTLEMENT_REPLAY_OBSERVATION_SEAL_V2,
        )


@pytest.mark.parametrize(
    ("field_name", "replacement", "expected_code"),
    (
        ("verified_program_id", _root("wrong-program"), "candidate_binding"),
        ("verified_profile_id", _root("wrong-policy-profile"), "candidate_binding"),
        (
            "verified_program_manifest_root",
            _root("wrong-program-manifest"),
            "candidate_binding",
        ),
        ("pre_state_root", _root("wrong-state"), "pre_state_root"),
    ),
)
def test_v2_replay_rejects_program_policy_and_state_substitution(
    field_name: str,
    replacement: str,
    expected_code: str,
) -> None:
    fixture = _fixture()
    candidate = replace(fixture.candidate, **{field_name: replacement})
    config = replay_engine_config_document_v0(DexEngineConfig(chain_id=_CHAIN_ID))
    adapter = SpotV7SettlementEnvelopeReplayAdapterV2(config)

    with pytest.raises(SpotV7SettlementEnvelopeReplayErrorV1) as captured:
        adapter.authenticate(
            settlement=_settlement(candidate),
            header=fixture.header,
            body=fixture.body,
            pre_snapshot=fixture.pre_snapshot,
        )

    assert captured.value.code == expected_code


def test_v2_replay_rejects_envelope_substitution() -> None:
    fixture = _fixture()
    body = copy.deepcopy(fixture.body)
    body["settlement_envelopes"][0]["proposal"]["economic_action_id"] = _root(
        "wrong-envelope-action"
    )
    config = replay_engine_config_document_v0(DexEngineConfig(chain_id=_CHAIN_ID))
    header = _header(fixture.candidate, body, config)

    with pytest.raises(SpotV7SettlementEnvelopeReplayErrorV1) as captured:
        SpotV7SettlementEnvelopeReplayAdapterV2(config).authenticate(
            settlement=fixture.settlement,
            header=header,
            body=body,
            pre_snapshot=fixture.pre_snapshot,
        )

    assert captured.value.code == "candidate_binding"


@pytest.mark.parametrize(
    "field_name",
    (
        "parent_header_hash",
        "body_root",
        "config_digest",
        "proof_journal_hash",
        "candidate_settlement_commitment",
        "envelope_proposal_hash",
        "receipt_hash",
        "settlement_effect_plan_commitment",
        "pre_state_root",
        "post_state_root",
        "economic_action_id",
        "authorization_nullifier",
        "authorization_grant_spend_nullifier",
        "cell_transitions_root",
        "asset_effect_ids_root",
    ),
)
def test_v2_constructor_rejects_projection_graph_substitution(field_name: str) -> None:
    _fixture_value, observation = _v2_observation()
    projection = observation._projection_for_finality_adapter()
    persisted = _v2_persisted_inputs(observation)
    substituted_projection = _replace_v2_projection_hash_field(
        projection,
        field_name,
        _root(field_name),
    )

    with pytest.raises(ValueError):
        replay_contract._AuthenticatedSpotV7SettlementReplayObservationV2(
            substituted_projection,
            exact_header_bytes=persisted.exact_header_bytes,
            exact_body_bytes=persisted.exact_body_bytes,
            exact_envelope_bytes=persisted.exact_envelope_bytes,
            exact_receipt_bytes=persisted.exact_receipt_bytes,
            exact_evidence_bytes=persisted.exact_evidence_bytes,
            exact_config_document_bytes=persisted.exact_config_document_bytes,
            exact_pre_state_snapshot_bytes=persisted.exact_pre_state_snapshot_bytes,
            seal=replay_contract._SETTLEMENT_REPLAY_OBSERVATION_SEAL_V2,
        )


def _replace_v2_projection_hash_field(
    projection: replay_contract._SpotV7SettlementReplayProjectionV2,
    field_name: str,
    replacement: str,
) -> replay_contract._SpotV7SettlementReplayProjectionV2:
    replacements = {
        "parent_header_hash": lambda: replace(projection, parent_header_hash=replacement),
        "body_root": lambda: replace(projection, body_root=replacement),
        "config_digest": lambda: replace(projection, config_digest=replacement),
        "proof_journal_hash": lambda: replace(projection, proof_journal_hash=replacement),
        "candidate_settlement_commitment": lambda: replace(
            projection,
            candidate_settlement_commitment=replacement,
        ),
        "envelope_proposal_hash": lambda: replace(
            projection,
            envelope_proposal_hash=replacement,
        ),
        "receipt_hash": lambda: replace(projection, receipt_hash=replacement),
        "settlement_effect_plan_commitment": lambda: replace(
            projection,
            settlement_effect_plan_commitment=replacement,
        ),
        "pre_state_root": lambda: replace(projection, pre_state_root=replacement),
        "post_state_root": lambda: replace(projection, post_state_root=replacement),
        "economic_action_id": lambda: replace(projection, economic_action_id=replacement),
        "authorization_nullifier": lambda: replace(
            projection,
            authorization_nullifier=replacement,
        ),
        "authorization_grant_spend_nullifier": lambda: replace(
            projection,
            authorization_grant_spend_nullifier=replacement,
        ),
        "cell_transitions_root": lambda: replace(
            projection,
            cell_transitions_root=replacement,
        ),
        "asset_effect_ids_root": lambda: replace(
            projection,
            asset_effect_ids_root=replacement,
        ),
    }
    try:
        return replacements[field_name]()
    except KeyError as exc:
        raise AssertionError(f"unsupported test projection field: {field_name}") from exc


def test_v2_constructor_rejects_coherently_rehashed_body_envelope_substitution() -> None:
    _fixture_value, observation = _v2_observation()
    projection = observation._projection_for_finality_adapter()
    persisted = _v2_persisted_inputs(observation)
    body = json.loads(persisted.exact_body_bytes)
    body["settlement_envelopes"][0]["proposal"]["economic_action_id"] = _root(
        "coherent-body-only-action"
    )
    body_bytes = canonical_json_bytes_v0(body)
    body_root = canonical_body_root_v0(body)
    header = json.loads(persisted.exact_header_bytes)
    header["body_root"] = body_root
    header_bytes = canonical_json_bytes_v0(header)
    header_hash = canonical_header_hash_v0(header)
    evidence = json.loads(persisted.exact_evidence_bytes)
    evidence["body_root"] = body_root
    evidence["header_hash"] = header_hash
    evidence_bytes = canonical_json_bytes_v0(evidence)
    substituted_projection = replace(
        projection,
        body_root=body_root,
        header_hash=header_hash,
        observation_evidence_root=_prefixed_sha256(evidence_bytes),
    )

    with pytest.raises(ValueError, match="body envelope disagrees"):
        replay_contract._AuthenticatedSpotV7SettlementReplayObservationV2(
            substituted_projection,
            exact_header_bytes=header_bytes,
            exact_body_bytes=body_bytes,
            exact_envelope_bytes=persisted.exact_envelope_bytes,
            exact_receipt_bytes=persisted.exact_receipt_bytes,
            exact_evidence_bytes=evidence_bytes,
            exact_config_document_bytes=persisted.exact_config_document_bytes,
            exact_pre_state_snapshot_bytes=persisted.exact_pre_state_snapshot_bytes,
            seal=replay_contract._SETTLEMENT_REPLAY_OBSERVATION_SEAL_V2,
        )


def test_v2_constructor_rejects_coherently_rehashed_envelope_receipt_substitution() -> None:
    _fixture_value, observation = _v2_observation()
    projection = observation._projection_for_finality_adapter()
    persisted = _v2_persisted_inputs(observation)
    envelope = json.loads(persisted.exact_envelope_bytes)
    envelope["expected_receipt"]["economic_action_id"] = _root("coherent-envelope-only-action")
    envelope_bytes = canonical_json_bytes_v0(envelope)
    body = json.loads(persisted.exact_body_bytes)
    body["settlement_envelopes"] = [envelope]
    body_bytes = canonical_json_bytes_v0(body)
    body_root = canonical_body_root_v0(body)
    header = json.loads(persisted.exact_header_bytes)
    header["body_root"] = body_root
    header_bytes = canonical_json_bytes_v0(header)
    header_hash = canonical_header_hash_v0(header)
    envelope_sha256 = _prefixed_sha256(envelope_bytes)
    evidence = json.loads(persisted.exact_evidence_bytes)
    evidence["body_root"] = body_root
    evidence["header_hash"] = header_hash
    evidence["envelope_sha256"] = envelope_sha256
    evidence_bytes = canonical_json_bytes_v0(evidence)
    substituted_projection = replace(
        projection,
        body_root=body_root,
        header_hash=header_hash,
        envelope_sha256=envelope_sha256,
        observation_evidence_root=_prefixed_sha256(evidence_bytes),
    )

    with pytest.raises(ValueError, match="envelope receipt disagrees"):
        replay_contract._AuthenticatedSpotV7SettlementReplayObservationV2(
            substituted_projection,
            exact_header_bytes=header_bytes,
            exact_body_bytes=body_bytes,
            exact_envelope_bytes=envelope_bytes,
            exact_receipt_bytes=persisted.exact_receipt_bytes,
            exact_evidence_bytes=evidence_bytes,
            exact_config_document_bytes=persisted.exact_config_document_bytes,
            exact_pre_state_snapshot_bytes=persisted.exact_pre_state_snapshot_bytes,
            seal=replay_contract._SETTLEMENT_REPLAY_OBSERVATION_SEAL_V2,
        )


def test_v2_observation_rejects_copy_pickle_mutation_and_forgery() -> None:
    _fixture_value, observation = _v2_observation()
    persisted = _v2_persisted_inputs(observation)

    with pytest.raises(TypeError):
        copy.copy(observation)
    with pytest.raises(TypeError):
        copy.deepcopy(observation)
    with pytest.raises(TypeError):
        pickle.dumps(observation)
    with pytest.raises(TypeError):
        mutable_view = cast(Any, observation)
        mutable_view._projection = observation._projection_for_finality_adapter()
    with pytest.raises(TypeError):
        replay_contract._AuthenticatedSpotV7SettlementReplayObservationV2(
            observation._projection_for_finality_adapter(),
            exact_header_bytes=persisted.exact_header_bytes,
            exact_body_bytes=persisted.exact_body_bytes,
            exact_envelope_bytes=persisted.exact_envelope_bytes,
            exact_receipt_bytes=persisted.exact_receipt_bytes,
            exact_evidence_bytes=persisted.exact_evidence_bytes,
            exact_config_document_bytes=persisted.exact_config_document_bytes,
            exact_pre_state_snapshot_bytes=persisted.exact_pre_state_snapshot_bytes,
            seal=cast(replay_contract._SettlementReplayObservationSealV2, object()),
        )

    forged = object.__new__(replay_contract._AuthenticatedSpotV7SettlementReplayObservationV2)
    with pytest.raises(TypeError):
        replay_contract._require_settlement_replay_observation_v2(forged)
    with pytest.raises(TypeError):
        _ = forged.exact_replay_material_authenticated


def test_v1_replay_observation_behavior_and_claim_scope_are_unchanged() -> None:
    fixture = _fixture()

    observation = fixture.adapter.authenticate(
        settlement=fixture.settlement,
        header=fixture.header,
        body=fixture.body,
        pre_snapshot=fixture.pre_snapshot,
    )

    assert type(observation) is replay_contract._AuthenticatedSpotV7SettlementReplayObservationV1
    assert not hasattr(observation, "_exact_replay_material_for_history_reverification")
    assert observation.settlement_authority is False
    assert observation.release_authority is False
    assert observation.production_authority is False
