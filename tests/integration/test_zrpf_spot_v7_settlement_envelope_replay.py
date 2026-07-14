"""CBC tests for bounded Spot V7 settlement-envelope replay."""

from __future__ import annotations

import copy
import hashlib
import json
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Any

import pytest

import src.integration._zrpf_spot_v7_firecracker_authority as firecracker_authority
from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _candidate_action_ids_root,
    _SpotV7SettlementCandidateInputV1,
)
from src.integration._zrpf_spot_v7_firecracker_authority import (
    _GovernedFirecrackerSpotV7SettlementV1,
)
from src.integration._zrpf_spot_v7_settlement_envelope_replay import (
    SpotV7SettlementEnvelopeReplayAdapterV1,
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
        (("proposal", "ingress_nonce"), 8, "candidate_binding"),
        (("proposal", "cell_transitions", 0, "post", "atoms"), 2_093, "candidate_binding"),
        (("proposal", "asset_effects", 0, "amount_atoms"), 999, "candidate_binding"),
        (("expected_receipt", "economic_action_id"), _root("wrong-receipt"), "committed_receipt"),
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
