"""CBC tests for the private Spot V7 replay-bound ledger observation."""

from __future__ import annotations

import copy
import hashlib
import pickle
from unittest.mock import Mock

import pytest

import src.integration._zrpf_spot_v7_zeno_ledger_replay_observation as replay_module
from src.core.dex import DexState
from src.integration._zrpf_spot_v7_zeno_ledger_replay_contract import (
    SPOT_V7_ZENO_LEDGER_BODY_PROOF_RECEIPT_PROJECTION_SCHEMA_V1,
    SPOT_V7_ZENO_LEDGER_RECEIPTS_ROOT_DOMAIN_V1,
    SPOT_V7_ZENO_LEDGER_REJECTIONS_ROOT_DOMAIN_V1,
)
from src.integration._zrpf_spot_v7_zeno_ledger_replay_observation import (
    SpotV7ZenoLedgerReplayBoundObservationAdapterV1,
    SpotV7ZenoLedgerReplayObservationErrorV1,
    _AuthenticatedReplayBoundBlockObservationV1,
)
from src.integration.dex_engine import DexEngineConfig
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.zeno_ledger_replay import (
    replay_engine_config_digest_v0,
    replay_engine_config_document_v0,
)
from src.integration.zeno_ledger_v0 import (
    BATCH_CUTOFF_SCHEMA_V0,
    BODY_SCHEMA_V0,
    apply_body_transactions_v0,
    build_header_v0,
    canonical_body_root_v0,
    compute_app_hash_v0,
    compute_evidence_root_v0,
    compute_ingress_root_v0,
    compute_tx_root_v0,
    dex_state_root_v0,
    hash_v0,
)
from src.state.balances import BalanceTable
from src.state.lp import LPTable

ZERO_ROOT = "0x" + "00" * 32
CHAIN_ID = "zeno-ledger-zrpf-replay-observation-test-v1"


def _root(label: str) -> str:
    return hash_v0("zrpf_spot_v7_replay_observation_test_root", {"label": label})


def _state() -> DexState:
    return DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())


def _body(*, proof_journal_hash: str | None = None) -> dict[str, object]:
    return {
        "schema": BODY_SCHEMA_V0,
        "chain_id": CHAIN_ID,
        "height": 1,
        "ingress": {
            "batch_cutoff": {
                "schema": BATCH_CUTOFF_SCHEMA_V0,
                "chain_id": CHAIN_ID,
                "height": 1,
                "cutoff_time_ms": 1_784_000_000_001,
                "cutoff_sequence": 1,
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
                    "proof_journal_hash": proof_journal_hash
                    or _root("proof-journal"),
                }
            ],
            "rejection_receipts": [],
        },
    }


def _config_document() -> dict[str, object]:
    return replay_engine_config_document_v0(DexEngineConfig(chain_id=CHAIN_ID))


def _header(
    *,
    body: dict[str, object],
    state_root: str,
    config_digest: str,
    pre_state_root: str | None = None,
) -> dict[str, object]:
    evidence = body["evidence"]
    ingress = body["ingress"]
    transactions = body["transactions"]
    assert isinstance(evidence, dict)
    assert isinstance(ingress, dict)
    assert isinstance(transactions, list)
    evidence_root = compute_evidence_root_v0(evidence)
    module_versions_digest = _root("modules")
    app_hash = compute_app_hash_v0(
        {
            "chain_id": CHAIN_ID,
            "height": 1,
            "post_state_root": state_root,
            "evidence_root": evidence_root,
            "config_digest": config_digest,
            "module_versions_digest": module_versions_digest,
        }
    )
    return build_header_v0(
        chain_id=CHAIN_ID,
        height=1,
        time_ms=1_784_000_000_001,
        prev_header_hash=_root("genesis"),
        sequencer_set_hash=_root("scheduled-validator-set"),
        ingress_root=compute_ingress_root_v0(ingress),
        tx_root=compute_tx_root_v0(transactions),
        pre_state_root=pre_state_root or state_root,
        post_state_root=state_root,
        app_hash=app_hash,
        evidence_root=evidence_root,
        body_root=canonical_body_root_v0(body),
        data_availability_root=_root("data"),
        proof_journal_hash=_root("proof-journal"),
        config_digest=config_digest,
        module_versions_digest=module_versions_digest,
        signature_set_root=ZERO_ROOT,
    )


def _fixture() -> tuple[
    SpotV7ZenoLedgerReplayBoundObservationAdapterV1,
    dict[str, object],
    dict[str, object],
    dict[str, object],
]:
    state = _state()
    state_root = dex_state_root_v0(state)
    body = _body()
    config_document = _config_document()
    config_digest = replay_engine_config_digest_v0(config_document)
    return (
        SpotV7ZenoLedgerReplayBoundObservationAdapterV1(config_document),
        _header(body=body, state_root=state_root, config_digest=config_digest),
        body,
        snapshot_from_state(state).data,
    )


def test_deterministic_replay_mints_one_private_observation() -> None:
    adapter, header, body, snapshot = _fixture()

    observation = adapter.authenticate(
        header=header,
        body=body,
        pre_snapshot=snapshot,
    )

    assert type(observation) is _AuthenticatedReplayBoundBlockObservationV1
    assert observation._has_private_seal() is True
    projection = observation._projection_for_finality_adapter()
    assert projection.header_hash == observation._projection.header_hash
    assert projection.body_root == header["body_root"]
    assert projection.config_digest == header["config_digest"]
    assert projection.pre_state_root == header["pre_state_root"]
    assert projection.post_state_root == header["post_state_root"]
    assert projection.replayed_receipt_count == 0
    assert projection.replayed_rejection_count == 0
    assert projection.committed_proof_receipt_count == 1
    assert projection.body_committed_proof_journal_hash == header["proof_journal_hash"]
    assert projection.body_sha256 == (
        "0x" + hashlib.sha256(observation._exact_body_bytes).hexdigest()
    )
    assert observation.settlement_authority is False
    assert observation.production_authority is False


def test_one_observation_invokes_deterministic_replay_exactly_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    adapter, header, body, snapshot = _fixture()
    replay = Mock(wraps=replay_module._replay_bound_block_details_v0)
    monkeypatch.setattr(replay_module, "_replay_bound_block_details_v0", replay)

    adapter.authenticate(header=header, body=body, pre_snapshot=snapshot)

    assert replay.call_count == 1


def test_nonempty_accept_and_reject_receipts_are_bound_exactly() -> None:
    state = _state()
    config = DexEngineConfig(chain_id=CHAIN_ID)
    config_document = replay_engine_config_document_v0(config)
    body = _body()
    body["transactions"] = [
        {"operations": {}, "block_timestamp": 1_784_000_000_001},
        {"sender": "rejected", "nonce": 1},
    ]
    _post_state, executed_body, receipts = apply_body_transactions_v0(
        state=state,
        body=body,
        config=config,
    )
    config_digest = replay_engine_config_digest_v0(config_document)
    header = _header(
        body=executed_body,
        state_root=dex_state_root_v0(state),
        config_digest=config_digest,
    )

    observation = SpotV7ZenoLedgerReplayBoundObservationAdapterV1(
        config_document
    ).authenticate(
        header=header,
        body=executed_body,
        pre_snapshot=snapshot_from_state(state).data,
    )

    projection = observation._projection_for_finality_adapter()
    assert [receipt["accepted"] for receipt in receipts] == [True, False]
    assert projection.replayed_receipt_count == 2
    assert projection.replayed_rejection_count == 1
    assert projection.replayed_receipts_root == hash_v0(
        SPOT_V7_ZENO_LEDGER_RECEIPTS_ROOT_DOMAIN_V1,
        {"receipts": receipts},
    )
    assert projection.replayed_rejections_root == hash_v0(
        SPOT_V7_ZENO_LEDGER_REJECTIONS_ROOT_DOMAIN_V1,
        {
            "rejection_receipts": executed_body["evidence"][
                "rejection_receipts"
            ]
        },
    )


@pytest.mark.parametrize(
    "untrusted",
    (
        {"state_replay_checked": True, "receipt_replay_checked": True},
        {"ok": True, "body_bound": True},
        b"caller-authored-replay-report",
        True,
    ),
)
def test_caller_reports_cannot_become_private_observations(untrusted: object) -> None:
    with pytest.raises(TypeError):
        _AuthenticatedReplayBoundBlockObservationV1(
            untrusted,  # type: ignore[arg-type]
            exact_header_bytes=b"{}",
            exact_body_bytes=b"{}",
            exact_evidence_bytes=b"{}",
            seal=object(),  # type: ignore[arg-type]
        )


def test_body_substitution_rejects_before_observation_mint() -> None:
    adapter, header, body, snapshot = _fixture()
    substituted = copy.deepcopy(body)
    substituted["transactions"] = [{"nonce": 1}]

    with pytest.raises(SpotV7ZenoLedgerReplayObservationErrorV1) as captured:
        adapter.authenticate(header=header, body=substituted, pre_snapshot=snapshot)

    assert captured.value.code == "body_binding"


def test_config_digest_mismatch_rejects_before_observation_mint() -> None:
    adapter, header, body, snapshot = _fixture()
    header["config_digest"] = _root("forged-config")

    with pytest.raises(SpotV7ZenoLedgerReplayObservationErrorV1) as captured:
        adapter.authenticate(header=header, body=body, pre_snapshot=snapshot)

    assert captured.value.code == "config_digest"


def test_state_continuity_mismatch_rejects_before_observation_mint() -> None:
    adapter, header, body, snapshot = _fixture()
    header["pre_state_root"] = _root("forged-pre-state")

    with pytest.raises(SpotV7ZenoLedgerReplayObservationErrorV1) as captured:
        adapter.authenticate(header=header, body=body, pre_snapshot=snapshot)

    assert captured.value.code == "state_continuity"


def test_rejection_receipt_substitution_rejects_before_observation_mint() -> None:
    adapter, _header_value, body, snapshot = _fixture()
    evidence = body["evidence"]
    assert isinstance(evidence, dict)
    evidence["rejection_receipts"] = [{"receipt_root": _root("forged-reject")}]
    config_document = _config_document()
    config_digest = replay_engine_config_digest_v0(config_document)
    state_root = dex_state_root_v0(_state())
    header = _header(body=body, state_root=state_root, config_digest=config_digest)

    with pytest.raises(SpotV7ZenoLedgerReplayObservationErrorV1) as captured:
        adapter.authenticate(header=header, body=body, pre_snapshot=snapshot)

    assert captured.value.code == "rejection_receipts"


def test_post_replay_proof_projection_failure_is_a_typed_reject() -> None:
    adapter, _header_value, body, snapshot = _fixture()
    evidence = body["evidence"]
    assert isinstance(evidence, dict)
    evidence["proof_receipts"] = [{"proof_journal_hash": _root("proof-journal")}]
    config_document = _config_document()
    config_digest = replay_engine_config_digest_v0(config_document)
    state_root = dex_state_root_v0(_state())
    header = _header(body=body, state_root=state_root, config_digest=config_digest)

    with pytest.raises(SpotV7ZenoLedgerReplayObservationErrorV1) as captured:
        adapter.authenticate(header=header, body=body, pre_snapshot=snapshot)

    assert captured.value.code == "proof_receipt_projection"


def test_snapshot_failure_is_a_typed_reject() -> None:
    adapter, header, body, _snapshot = _fixture()

    with pytest.raises(SpotV7ZenoLedgerReplayObservationErrorV1) as captured:
        adapter.authenticate(header=header, body=body, pre_snapshot=True)

    assert captured.value.code == "state_continuity"


def test_private_observation_is_not_transferable() -> None:
    adapter, header, body, snapshot = _fixture()
    observation = adapter.authenticate(header=header, body=body, pre_snapshot=snapshot)

    for transfer in (copy.copy, copy.deepcopy, pickle.dumps):
        with pytest.raises(TypeError):
            transfer(observation)
    with pytest.raises(TypeError):
        observation._projection = observation._projection


def test_replay_adapter_configuration_is_immutable_and_nontransferable() -> None:
    adapter, _header_value, _body_value, _snapshot = _fixture()

    for transfer in (copy.copy, copy.deepcopy, pickle.dumps):
        with pytest.raises(TypeError):
            transfer(adapter)
    with pytest.raises(TypeError):
        adapter._config_digest = adapter._config_digest
    with pytest.raises(TypeError):
        adapter._config_document_bytes = b"{}"
