from __future__ import annotations

from copy import deepcopy

import pytest

from src.core.cross_shard_decision_certificate import (
    CrossShardDecisionParticipantV1,
    CrossShardDecisionState,
    CrossShardReceiptStatus,
    ParticipantPrepareState,
    ParticipantVisibilityState,
    build_cross_shard_decision_certificate,
)
from src.core.cross_shard_ledger_effects import (
    CROSS_SHARD_CREDIT_ESCROW_ACCOUNT_V1,
    CROSS_SHARD_DEBIT_ESCROW_ACCOUNT_V1,
)
from src.core.cross_shard_ledger_posting import (
    CrossShardLedgerPostingBuildResult,
    CrossShardLedgerPostingSummaryV1,
    build_cross_shard_ledger_posting_summary,
)
from src.core.cross_shard_settlement_admission import (
    verify_cross_shard_settlement_admission_payload,
)
from src.core.sharded_settlement_certificate import (
    CrossShardLegV1,
    ShardedSettlementShardV1,
    build_sharded_settlement_certificate,
    sharded_settlement_certificate_hash,
)
from src.integration.zeno_ledger_cross_shard_effect_application import (
    apply_cross_shard_ledger_effects_to_balances_v0,
    apply_cross_shard_ledger_effects_to_state_v0,
    apply_terminal_cross_shard_ledger_effects_to_balances_v0,
    apply_terminal_cross_shard_ledger_effects_to_state_v0,
    build_cross_shard_ledger_effects_artifact_v0,
    build_cross_shard_terminal_decision_effect_admission_v0,
    compute_cross_shard_applied_effects_state_root_v0,
    cross_shard_applied_effects_state_from_payload_v0,
    empty_cross_shard_applied_effects_state_v0,
    validate_cross_shard_ledger_effects_artifact_v0,
    validate_cross_shard_terminal_decision_effect_admission_v0,
    verify_cross_shard_terminal_decision_effect_admission_source_v0,
)
from src.integration.zeno_ledger_tau_export import (
    build_cross_shard_posting_summary_export_v0,
)
from src.integration.zeno_ledger_v0 import (
    TAU_APP_STATE_SCHEMA_V1,
    app_root_lanes_from_tau_app_state_v0,
    compute_tau_app_state_app_root_v0,
    hash_v0,
)
from src.state.balances import BalanceTable

_SETTLEMENT_CERT_HASH = "0x" + "e" * 64


def _posting_summary() -> dict[str, object]:
    posting_result = CrossShardLedgerPostingBuildResult(
        ok=True,
        error=None,
        sharded_settlement_certificate_hash=_SETTLEMENT_CERT_HASH,
        postings=(
            CrossShardLedgerPostingSummaryV1(
                asset_id="quote",
                committed_debit_atoms=1_000,
                committed_credit_atoms=1_000,
            ),
        ),
        total_committed_debit_atoms=1_000,
        total_committed_credit_atoms=1_000,
    )
    return build_cross_shard_posting_summary_export_v0(posting_result=posting_result)


def _artifact() -> dict[str, object]:
    return build_cross_shard_ledger_effects_artifact_v0(
        posting_summary=_posting_summary()
    )


def _hash(label: str) -> str:
    return hash_v0("cross_shard_terminal_admission_test", {"label": label})


def _participant(
    shard_id: str,
    *,
    prepared: bool,
    visible: bool,
) -> CrossShardDecisionParticipantV1:
    return CrossShardDecisionParticipantV1(
        shard_id=shard_id,
        prepare_state=(
            ParticipantPrepareState.PREPARED
            if prepared
            else ParticipantPrepareState.UNPREPARED
        ),
        visibility_state=(
            ParticipantVisibilityState.VISIBLE
            if visible
            else ParticipantVisibilityState.HIDDEN
        ),
    )


def _participants(
    *,
    prepared: bool,
    visible: bool,
) -> tuple[CrossShardDecisionParticipantV1, ...]:
    return (
        _participant("shard-a", prepared=prepared, visible=visible),
        _participant("shard-b", prepared=prepared, visible=visible),
    )


def _terminal_sharded_payload(*, amount_atoms: int = 1_000) -> dict[str, object]:
    cert = build_sharded_settlement_certificate(
        batch_id="batch-1",
        shards=(
            ShardedSettlementShardV1(
                shard_id="shard-a",
                settlement_root_hash=_hash("shard-a"),
                dx_atoms=0,
                dy_atoms=0,
            ),
            ShardedSettlementShardV1(
                shard_id="shard-b",
                settlement_root_hash=_hash("shard-b"),
                dx_atoms=0,
                dy_atoms=0,
            ),
        ),
        cross_shard_legs=(
            CrossShardLegV1(
                transfer_id="transfer-1",
                side="credit",
                shard_id="shard-b",
                counterparty_shard_id="shard-a",
                asset_id="quote",
                amount_atoms=amount_atoms,
            ),
            CrossShardLegV1(
                transfer_id="transfer-1",
                side="debit",
                shard_id="shard-a",
                counterparty_shard_id="shard-b",
                asset_id="quote",
                amount_atoms=amount_atoms,
            ),
        ),
    )
    return cert.to_payload()


def _terminal_decision_payload(
    sharded_payload: dict[str, object],
    *,
    receipt_status: CrossShardReceiptStatus = CrossShardReceiptStatus.MATCHED,
    decision: CrossShardDecisionState = CrossShardDecisionState.COMMIT,
    prepared: bool = True,
    visible: bool = True,
) -> dict[str, object]:
    cert = build_cross_shard_decision_certificate(
        batch_id="batch-1",
        transfer_id="transfer-1",
        sharded_settlement_certificate_hash=sharded_settlement_certificate_hash(
            sharded_payload
        ),
        receipt_status=receipt_status,
        decision=decision,
        participants=_participants(prepared=prepared, visible=visible),
        decision_step=1,
        deadline_step=3,
    )
    return cert.to_payload()


def _terminal_source_bundle() -> tuple[
    dict[str, object],
    dict[str, object],
    dict[str, object],
    dict[str, object],
    tuple[dict[str, object], ...],
]:
    sharded_payload = _terminal_sharded_payload()
    decision_payload = _terminal_decision_payload(sharded_payload)
    admission = verify_cross_shard_settlement_admission_payload(
        sharded_payload,
        decision_certificate_payloads=(decision_payload,),
        current_step=1,
    )
    assert admission.ok is True
    posting_result = build_cross_shard_ledger_posting_summary(admission)
    assert posting_result.ok is True
    posting_summary = build_cross_shard_posting_summary_export_v0(
        posting_result=posting_result
    )
    effects_artifact = build_cross_shard_ledger_effects_artifact_v0(
        posting_summary=posting_summary
    )
    terminal_admission = build_cross_shard_terminal_decision_effect_admission_v0(
        sharded_settlement_payload=sharded_payload,
        decision_certificate_payloads=(decision_payload,),
        posting_summary=posting_summary,
        effects_artifact=effects_artifact,
        current_step=1,
    )
    return (
        posting_summary,
        effects_artifact,
        terminal_admission,
        sharded_payload,
        (decision_payload,),
    )


def _terminal_bundle() -> tuple[dict[str, object], dict[str, object], dict[str, object]]:
    posting_summary, effects_artifact, terminal_admission, _sharded_payload, _decision_payloads = (
        _terminal_source_bundle()
    )
    return posting_summary, effects_artifact, terminal_admission


def _seeded_balances(*, debit_atoms: int = 1_000) -> BalanceTable:
    balances = BalanceTable()
    balances.set(CROSS_SHARD_DEBIT_ESCROW_ACCOUNT_V1, "quote", debit_atoms)
    balances.set(CROSS_SHARD_CREDIT_ESCROW_ACCOUNT_V1, "quote", 7)
    return balances


def _dex_snapshot() -> dict[str, object]:
    return {
        "version": 4,
        "balances": [],
        "pools": [],
        "lp_balances": [],
        "lp_mint_timestamps": [],
        "lp_duration_risk": [],
        "nonces": [],
        "fee_accumulator": {"dust": 0},
        "vault": None,
        "oracle": None,
        "perps": None,
    }


def _tau_app_state(cross_shard_state: object = None) -> dict[str, object]:
    out: dict[str, object] = {
        "schema": TAU_APP_STATE_SCHEMA_V1,
        "version": 1,
        "dex_state": _dex_snapshot(),
    }
    if cross_shard_state is not None:
        out["cross_shard"] = cross_shard_state
    return out


def test_build_and_validate_cross_shard_effects_artifact() -> None:
    artifact = _artifact()

    assert validate_cross_shard_ledger_effects_artifact_v0(artifact) == artifact
    assert artifact["effect_count"] == 2
    assert artifact["total_debit_atoms"] == 1_000
    assert artifact["total_credit_atoms"] == 1_000
    assert artifact["source_posting_summary_hash"] == _posting_summary()["posting_summary_hash"]


def test_cross_shard_applied_effects_state_roundtrip_and_root() -> None:
    empty = empty_cross_shard_applied_effects_state_v0()
    artifact = _artifact()
    updated = empty.add(str(artifact["ledger_effects_hash"]))

    restored = cross_shard_applied_effects_state_from_payload_v0(updated.to_payload())

    assert restored == updated
    assert compute_cross_shard_applied_effects_state_root_v0(restored) == updated.root_hash()
    assert compute_cross_shard_applied_effects_state_root_v0(empty) != updated.root_hash()


def test_tau_app_root_binds_cross_shard_replay_state_lane() -> None:
    artifact = _artifact()
    empty = empty_cross_shard_applied_effects_state_v0()
    updated = empty.add(str(artifact["ledger_effects_hash"]))

    missing_root = compute_tau_app_state_app_root_v0(_tau_app_state())
    empty_root = compute_tau_app_state_app_root_v0(_tau_app_state(empty.to_payload()))
    updated_root = compute_tau_app_state_app_root_v0(_tau_app_state(updated.to_payload()))
    leaves = app_root_lanes_from_tau_app_state_v0(_tau_app_state(updated.to_payload()))

    assert any(
        leaf.lane_kind == "cross_shard" and leaf.lane_id == "global"
        for leaf in leaves
    )
    assert missing_root != empty_root
    assert empty_root != updated_root


def test_cross_shard_applied_effects_state_rejects_noncanonical_payload() -> None:
    hash_a = hash_v0("test", {"h": "a"})
    hash_b = hash_v0("test", {"h": "b"})

    for payload in (
        {
            "schema": "zenodex/zeno_ledger/cross_shard_applied_effects_state/v0",
            "applied_ledger_effect_hashes": [hash_b, hash_a],
        },
        {
            "schema": "zenodex/zeno_ledger/cross_shard_applied_effects_state/v0",
            "applied_ledger_effect_hashes": [hash_a, hash_a],
        },
    ):
        try:
            cross_shard_applied_effects_state_from_payload_v0(payload)
        except ValueError as exc:
            assert "applied_ledger_effect_hashes must" in str(exc)
        else:
            raise AssertionError("expected noncanonical replay state payload to reject")


def test_apply_cross_shard_effects_moves_escrow_balances_once() -> None:
    artifact = _artifact()
    balances = _seeded_balances()

    result = apply_cross_shard_ledger_effects_to_balances_v0(
        balances=balances,
        effects_artifact=artifact,
        body_pinned_posting_summary_hash=str(artifact["source_posting_summary_hash"]),
        applied_ledger_effect_hashes=frozenset(),
    )

    assert result.ok is True
    assert result.error is None
    assert result.applied_ledger_effect_hashes == frozenset(
        {str(artifact["ledger_effects_hash"])}
    )
    assert result.applied_effect_count == 2
    assert balances.get(CROSS_SHARD_DEBIT_ESCROW_ACCOUNT_V1, "quote") == 0
    assert balances.get(CROSS_SHARD_CREDIT_ESCROW_ACCOUNT_V1, "quote") == 1_007


def test_terminal_decision_admission_roundtrip_and_apply() -> None:
    (
        posting_summary,
        effects_artifact,
        terminal_admission,
        sharded_payload,
        decision_payloads,
    ) = _terminal_source_bundle()
    balances = _seeded_balances()

    assert validate_cross_shard_terminal_decision_effect_admission_v0(
        terminal_admission,
        posting_summary=posting_summary,
        effects_artifact=effects_artifact,
    ) == terminal_admission
    assert verify_cross_shard_terminal_decision_effect_admission_source_v0(
        terminal_admission,
        posting_summary=posting_summary,
        effects_artifact=effects_artifact,
        sharded_settlement_payload=sharded_payload,
        decision_certificate_payloads=decision_payloads,
    ) == terminal_admission

    result = apply_terminal_cross_shard_ledger_effects_to_balances_v0(
        balances=balances,
        effects_artifact=effects_artifact,
        body_pinned_posting_summary_hash=str(posting_summary["posting_summary_hash"]),
        applied_ledger_effect_hashes=frozenset(),
        terminal_admission=terminal_admission,
        posting_summary=posting_summary,
        sharded_settlement_payload=sharded_payload,
        decision_certificate_payloads=decision_payloads,
    )

    assert result.ok is True
    assert result.error is None
    assert result.applied_effect_count == 2
    assert balances.get(CROSS_SHARD_DEBIT_ESCROW_ACCOUNT_V1, "quote") == 0
    assert balances.get(CROSS_SHARD_CREDIT_ESCROW_ACCOUNT_V1, "quote") == 1_007


def test_terminal_state_apply_exposes_admission_hash() -> None:
    (
        posting_summary,
        effects_artifact,
        terminal_admission,
        sharded_payload,
        decision_payloads,
    ) = _terminal_source_bundle()
    balances = _seeded_balances()

    result = apply_terminal_cross_shard_ledger_effects_to_state_v0(
        balances=balances,
        effects_artifact=effects_artifact,
        body_pinned_posting_summary_hash=str(posting_summary["posting_summary_hash"]),
        replay_state=empty_cross_shard_applied_effects_state_v0(),
        terminal_admission=terminal_admission,
        posting_summary=posting_summary,
        sharded_settlement_payload=sharded_payload,
        decision_certificate_payloads=decision_payloads,
    )

    assert result.ok is True
    assert result.terminal_admission_hash == terminal_admission["admission_hash"]
    assert result.post_replay_state is not None
    assert result.post_replay_state.contains(str(effects_artifact["ledger_effects_hash"]))


def test_terminal_apply_requires_source_payloads_without_mutating() -> None:
    posting_summary, effects_artifact, terminal_admission = _terminal_bundle()
    balances = _seeded_balances()
    before = balances.get_all_balances()

    result = apply_terminal_cross_shard_ledger_effects_to_balances_v0(
        balances=balances,
        effects_artifact=effects_artifact,
        body_pinned_posting_summary_hash=str(posting_summary["posting_summary_hash"]),
        applied_ledger_effect_hashes=frozenset(),
        terminal_admission=terminal_admission,
        posting_summary=posting_summary,
    )

    assert result.ok is False
    assert result.error == (
        "terminal decision source payloads required before applying cross-shard ledger effects"
    )
    assert balances.get_all_balances() == before


def test_terminal_apply_rejects_mismatched_decision_source_without_mutating() -> None:
    (
        posting_summary,
        effects_artifact,
        terminal_admission,
        sharded_payload,
        _decision_payloads,
    ) = _terminal_source_bundle()
    reject_payload = _terminal_decision_payload(
        sharded_payload,
        receipt_status=CrossShardReceiptStatus.REJECTED,
        decision=CrossShardDecisionState.REJECT,
        prepared=False,
        visible=False,
    )
    balances = _seeded_balances()
    before = balances.get_all_balances()

    result = apply_terminal_cross_shard_ledger_effects_to_balances_v0(
        balances=balances,
        effects_artifact=effects_artifact,
        body_pinned_posting_summary_hash=str(posting_summary["posting_summary_hash"]),
        applied_ledger_effect_hashes=frozenset(),
        terminal_admission=terminal_admission,
        posting_summary=posting_summary,
        sharded_settlement_payload=sharded_payload,
        decision_certificate_payloads=(reject_payload,),
    )

    assert result.ok is False
    assert result.error == "terminal decision admission posting summary mismatch"
    assert balances.get_all_balances() == before


def test_reject_decision_cannot_build_value_admission() -> None:
    posting_summary, effects_artifact, _terminal_admission = _terminal_bundle()
    sharded_payload = _terminal_sharded_payload()
    reject_payload = _terminal_decision_payload(
        sharded_payload,
        receipt_status=CrossShardReceiptStatus.REJECTED,
        decision=CrossShardDecisionState.REJECT,
        prepared=False,
        visible=False,
    )

    with pytest.raises(
        ValueError,
        match="terminal decision admission posting summary mismatch",
    ):
        build_cross_shard_terminal_decision_effect_admission_v0(
            sharded_settlement_payload=sharded_payload,
            decision_certificate_payloads=(reject_payload,),
            posting_summary=posting_summary,
            effects_artifact=effects_artifact,
            current_step=1,
        )


def test_terminal_admission_rejects_tampered_ledger_effect_hash_without_mutating() -> None:
    (
        posting_summary,
        effects_artifact,
        terminal_admission,
        sharded_payload,
        decision_payloads,
    ) = _terminal_source_bundle()
    tampered = deepcopy(terminal_admission)
    tampered["ledger_effects_hash"] = hash_v0("test", {"wrong": "effects"})
    balances = _seeded_balances()
    before = balances.get_all_balances()

    result = apply_terminal_cross_shard_ledger_effects_to_balances_v0(
        balances=balances,
        effects_artifact=effects_artifact,
        body_pinned_posting_summary_hash=str(posting_summary["posting_summary_hash"]),
        applied_ledger_effect_hashes=frozenset(),
        terminal_admission=tampered,
        posting_summary=posting_summary,
        sharded_settlement_payload=sharded_payload,
        decision_certificate_payloads=decision_payloads,
    )

    assert result.ok is False
    assert result.error == "terminal decision admission ledger effects hash mismatch"
    assert balances.get_all_balances() == before


def test_terminal_admission_replay_rejects_without_mutating() -> None:
    (
        posting_summary,
        effects_artifact,
        terminal_admission,
        sharded_payload,
        decision_payloads,
    ) = _terminal_source_bundle()
    balances = _seeded_balances()
    first = apply_terminal_cross_shard_ledger_effects_to_balances_v0(
        balances=balances,
        effects_artifact=effects_artifact,
        body_pinned_posting_summary_hash=str(posting_summary["posting_summary_hash"]),
        applied_ledger_effect_hashes=frozenset(),
        terminal_admission=terminal_admission,
        posting_summary=posting_summary,
        sharded_settlement_payload=sharded_payload,
        decision_certificate_payloads=decision_payloads,
    )
    before = balances.get_all_balances()

    replay = apply_terminal_cross_shard_ledger_effects_to_balances_v0(
        balances=balances,
        effects_artifact=effects_artifact,
        body_pinned_posting_summary_hash=str(posting_summary["posting_summary_hash"]),
        applied_ledger_effect_hashes=first.applied_ledger_effect_hashes,
        terminal_admission=terminal_admission,
        posting_summary=posting_summary,
        sharded_settlement_payload=sharded_payload,
        decision_certificate_payloads=decision_payloads,
    )

    assert replay.ok is False
    assert replay.error == "cross-shard ledger effects artifact already applied"
    assert balances.get_all_balances() == before


def test_apply_cross_shard_effects_updates_persistent_replay_state_root() -> None:
    artifact = _artifact()
    balances = _seeded_balances()
    replay_state = empty_cross_shard_applied_effects_state_v0()

    result = apply_cross_shard_ledger_effects_to_state_v0(
        balances=balances,
        effects_artifact=artifact,
        body_pinned_posting_summary_hash=str(artifact["source_posting_summary_hash"]),
        replay_state=replay_state,
    )

    assert result.ok is True
    assert result.error is None
    assert result.pre_replay_state_root == replay_state.root_hash()
    assert result.post_replay_state_root != result.pre_replay_state_root
    assert result.post_replay_state is not None
    assert result.post_replay_state.contains(str(artifact["ledger_effects_hash"]))
    assert result.post_replay_state.root_hash() == result.post_replay_state_root


def test_persistent_replay_state_blocks_restart_replay_without_mutating() -> None:
    artifact = _artifact()
    balances = _seeded_balances()
    first = apply_cross_shard_ledger_effects_to_state_v0(
        balances=balances,
        effects_artifact=artifact,
        body_pinned_posting_summary_hash=str(artifact["source_posting_summary_hash"]),
        replay_state=empty_cross_shard_applied_effects_state_v0(),
    )
    assert first.ok is True
    assert first.post_replay_state is not None
    restored_state = cross_shard_applied_effects_state_from_payload_v0(
        first.post_replay_state.to_payload()
    )
    before = balances.get_all_balances()

    replay = apply_cross_shard_ledger_effects_to_state_v0(
        balances=balances,
        effects_artifact=artifact,
        body_pinned_posting_summary_hash=str(artifact["source_posting_summary_hash"]),
        replay_state=restored_state,
    )

    assert replay.ok is False
    assert replay.error == "cross-shard ledger effects artifact already applied"
    assert balances.get_all_balances() == before


def test_apply_cross_shard_effects_rejects_replay_without_mutating() -> None:
    artifact = _artifact()
    balances = _seeded_balances()
    first = apply_cross_shard_ledger_effects_to_balances_v0(
        balances=balances,
        effects_artifact=artifact,
        body_pinned_posting_summary_hash=str(artifact["source_posting_summary_hash"]),
        applied_ledger_effect_hashes=frozenset(),
    )
    before = balances.get_all_balances()

    replay = apply_cross_shard_ledger_effects_to_balances_v0(
        balances=balances,
        effects_artifact=artifact,
        body_pinned_posting_summary_hash=str(artifact["source_posting_summary_hash"]),
        applied_ledger_effect_hashes=first.applied_ledger_effect_hashes,
    )

    assert replay.ok is False
    assert replay.error == "cross-shard ledger effects artifact already applied"
    assert balances.get_all_balances() == before


def test_apply_cross_shard_effects_rejects_unpinned_source_without_mutating() -> None:
    artifact = _artifact()
    balances = _seeded_balances()
    before = balances.get_all_balances()

    result = apply_cross_shard_ledger_effects_to_balances_v0(
        balances=balances,
        effects_artifact=artifact,
        body_pinned_posting_summary_hash=hash_v0("test", {"wrong": "source"}),
        applied_ledger_effect_hashes=frozenset(),
    )

    assert result.ok is False
    assert result.error == "cross-shard ledger effects source hash is not body-pinned"
    assert balances.get_all_balances() == before


def test_apply_cross_shard_effects_rejects_tampered_artifact_without_mutating() -> None:
    artifact = _artifact()
    tampered = deepcopy(artifact)
    tampered["effects"][0]["delta_atoms"] = -999  # type: ignore[index]
    balances = _seeded_balances()
    before = balances.get_all_balances()

    result = apply_cross_shard_ledger_effects_to_balances_v0(
        balances=balances,
        effects_artifact=tampered,
        body_pinned_posting_summary_hash=str(artifact["source_posting_summary_hash"]),
        applied_ledger_effect_hashes=frozenset(),
    )

    assert result.ok is False
    assert result.error == "cross-shard ledger effects debit total mismatch"
    assert balances.get_all_balances() == before


def test_apply_cross_shard_effects_rejects_underflow_without_mutating() -> None:
    artifact = _artifact()
    balances = _seeded_balances(debit_atoms=999)
    before = balances.get_all_balances()

    result = apply_cross_shard_ledger_effects_to_balances_v0(
        balances=balances,
        effects_artifact=artifact,
        body_pinned_posting_summary_hash=str(artifact["source_posting_summary_hash"]),
        applied_ledger_effect_hashes=frozenset(),
    )

    assert result.ok is False
    assert result.error == "cross-shard ledger effects would make balance negative"
    assert balances.get_all_balances() == before
