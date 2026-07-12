from __future__ import annotations

import json
import os
import sqlite3
from concurrent.futures import ThreadPoolExecutor
from dataclasses import replace
from pathlib import Path
from typing import Callable

import pytest

import src.core._zrpf_settlement_commit_authority as settlement_authority_module
import src.integration.zrpf_atomic_settlement_store as settlement_store_module
from src.core._zrpf_settlement_commit_authority import (
    SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1,
    SettlementSemanticBindingUnavailableV1,
    _AuthenticatedSettlementCommitV1,
    _bind_authenticated_settlement_commit_v1,
)
from src.core.recursive_stark_admission import (
    RecursiveStarkRootFacts,
    TrustedRecursiveStarkAdmissionPolicy,
    _AuthenticatedRecursiveStarkRootFacts,
    _mint_recursive_stark_root_facts_after_verification,
    _RecursiveStarkVerificationProvenance,
    recursive_child_verification_claims_root_v1,
    recursive_message_ids_root_v1,
    recursive_receipt_ids_root_v1,
)
from src.core.zrpf_settlement_effect_plan import (
    AssetEffectKindV1,
    AssetEffectV1,
    AuthorizationConsumptionV1,
    CarryEffectKindV1,
    CarryEffectV1,
    LedgerCellWriteV1,
    MessageEffectKindV1,
    MessageEffectV1,
    ProposedSettlementEffectPlanV1,
    RewardEffectV1,
    SettlementEffectPlanV1,
    authorization_consumption_nullifier_v1,
    build_settlement_effect_plan_v1,
)
from src.integration.zrpf_atomic_settlement_store import (
    ATOMIC_SETTLEMENT_STORE_APPLICATION_ID_V1,
    ATOMIC_SETTLEMENT_STORE_SCHEMA_VERSION_V1,
    SQLiteZrpfAtomicSettlementStoreV1,
    ZrpfAtomicSettlementDispositionV1,
    ZrpfAtomicSettlementRejectReasonV1,
    ZrpfAtomicSettlementStoreErrorV1,
)
from src.integration.zrpf_atomic_settlement_store_types import (
    DurableZrpfSettlementCursorV1,
)


def _hash(index: int) -> str:
    assert index > 0
    return f"0x{index:064x}"


def _authorization(
    *,
    action_id: str,
    grant_id: str,
    pre_state_root: str,
    nonce: int = 7,
) -> AuthorizationConsumptionV1:
    nullifier = authorization_consumption_nullifier_v1(
        application_id=_hash(1),
        chain_or_domain_id=_hash(2),
        economic_action_id=action_id,
        authorization_subject_id=_hash(20),
        authorization_grant_id=grant_id,
        authorization_scope_id=_hash(22),
        authorization_nonce=nonce,
        action_pre_state_root=pre_state_root,
    )
    return AuthorizationConsumptionV1(
        application_id=_hash(1),
        chain_or_domain_id=_hash(2),
        economic_action_id=action_id,
        authorization_subject_id=_hash(20),
        authorization_grant_id=grant_id,
        authorization_scope_id=_hash(22),
        authorization_nonce=nonce,
        action_pre_state_root=pre_state_root,
        authorization_nullifier=nullifier,
    )


def _plan(
    *,
    root: int = 30,
    epoch: int = 9,
    pre_state: int = 3,
    post_state: int = 4,
    ordinary_action: int = 10,
    authorized_action: int = 11,
    grant: int = 21,
    cell_base: int = 40,
) -> SettlementEffectPlanV1:
    ordinary_action_id = _hash(ordinary_action)
    authorized_action_id = _hash(authorized_action)
    authorization = _authorization(
        action_id=authorized_action_id,
        grant_id=_hash(grant),
        pre_state_root=_hash(pre_state),
    )
    proposal = ProposedSettlementEffectPlanV1(
        application_id=_hash(1),
        chain_or_domain_id=_hash(2),
        epoch_id=epoch,
        source_root_journal_hash=_hash(root),
        public_policy_hash=_hash(31),
        pre_state_root=_hash(pre_state),
        post_state_root=_hash(post_state),
        economic_action_ids=(authorized_action_id, ordinary_action_id),
        ledger_cell_writes=(
            LedgerCellWriteV1(
                economic_action_id=authorized_action_id,
                cell_key=_hash(cell_base + 3),
                pre_value_hash=_hash(cell_base + 4),
                post_value_hash=_hash(cell_base + 5),
            ),
            LedgerCellWriteV1(
                economic_action_id=ordinary_action_id,
                cell_key=_hash(cell_base),
                pre_value_hash=_hash(cell_base + 1),
                post_value_hash=_hash(cell_base + 2),
            ),
        ),
        asset_effects=(
            AssetEffectV1(
                kind=AssetEffectKindV1.AUTHORIZED_MINT,
                economic_action_id=authorized_action_id,
                asset_id=_hash(61),
                debit_atoms=0,
                credit_atoms=50,
                authorized_mint_atoms=50,
                authorized_burn_atoms=0,
                authority_scope_id=authorization.authorization_scope_id,
                authorization_nullifier=authorization.authorization_nullifier,
            ),
            AssetEffectV1(
                kind=AssetEffectKindV1.ORDINARY_TRANSFER,
                economic_action_id=ordinary_action_id,
                asset_id=_hash(60),
                debit_atoms=100,
                credit_atoms=100,
                authorized_mint_atoms=0,
                authorized_burn_atoms=0,
            ),
        ),
        authorization_consumptions=(authorization,),
        message_effects=(),
        carry_effects=(),
        reward_effects=(),
    )
    return build_settlement_effect_plan_v1(proposal)


def _facts(plan: SettlementEffectPlanV1) -> RecursiveStarkRootFacts:
    root = int(plan.source_root_journal_hash, 16)
    children = (_hash(root * 100 + 1), _hash(root * 100 + 2))
    receipts = (_hash(root * 100 + 3), _hash(root * 100 + 4))
    messages = tuple(row.message_id for row in plan.message_effects)
    return RecursiveStarkRootFacts(
        chain_id="zenodex-devnet",
        epoch_id=plan.epoch_id,
        proof_profile="recursive_epoch_v1",
        root_journal_hash=plan.source_root_journal_hash,
        verifier_set_root=_hash(10_001),
        public_policy_hash=plan.public_policy_hash,
        child_verification_claim_hashes=children,
        child_verification_claims_root=recursive_child_verification_claims_root_v1(children),
        accepted_receipt_ids=receipts,
        accepted_receipts_root=recursive_receipt_ids_root_v1(receipts),
        cross_shard_message_ids=messages,
        cross_shard_message_ids_root=recursive_message_ids_root_v1(messages),
    )


def _plan_with_every_row_family() -> SettlementEffectPlanV1:
    base = _plan()
    ordinary = next(
        row for row in base.asset_effects if row.kind is AssetEffectKindV1.ORDINARY_TRANSFER
    )
    reward_authorization = _authorization(
        action_id=ordinary.economic_action_id,
        grant_id=_hash(171),
        pre_state_root=base.pre_state_root,
        nonce=172,
    )
    reward_effect = replace(
        ordinary,
        kind=AssetEffectKindV1.AUTHORIZED_REWARD,
        authority_scope_id=reward_authorization.authorization_scope_id,
        authorization_nullifier=reward_authorization.authorization_nullifier,
    )
    message_action_id = _hash(12)
    message_asset_effect = AssetEffectV1(
        kind=AssetEffectKindV1.ORDINARY_TRANSFER,
        economic_action_id=message_action_id,
        asset_id=_hash(63),
        debit_atoms=75,
        credit_atoms=75,
        authorized_mint_atoms=0,
        authorized_burn_atoms=0,
    )
    message = MessageEffectV1(
        economic_action_id=message_asset_effect.economic_action_id,
        asset_effect_id=message_asset_effect.effect_id,
        source_domain_id=base.chain_or_domain_id,
        destination_domain_id=_hash(162),
        asset_id=message_asset_effect.asset_id,
        amount_atoms=message_asset_effect.debit_atoms,
        kind=MessageEffectKindV1.OUTBOX_ENQUEUE,
    )
    carry = CarryEffectV1(
        economic_action_id=message.economic_action_id,
        message_id=message.message_id,
        asset_id=message.asset_id,
        amount_atoms=message.amount_atoms,
        kind=CarryEffectKindV1.LOCK,
    )
    recipient_write = next(
        row
        for row in base.ledger_cell_writes
        if row.economic_action_id == reward_effect.economic_action_id
    )
    reward = RewardEffectV1(
        economic_action_id=reward_effect.economic_action_id,
        asset_effect_id=reward_effect.effect_id,
        recipient_cell_key=recipient_write.cell_key,
        asset_id=reward_effect.asset_id,
        amount_atoms=reward_effect.credit_atoms,
        authority_scope_id=reward_authorization.authorization_scope_id,
        authorization_nullifier=reward_authorization.authorization_nullifier,
    )
    asset_effects = tuple(
        reward_effect if row.effect_id == ordinary.effect_id else row for row in base.asset_effects
    ) + (message_asset_effect,)
    message_cell_write = LedgerCellWriteV1(
        economic_action_id=message_action_id,
        cell_key=_hash(90),
        pre_value_hash=_hash(91),
        post_value_hash=_hash(92),
    )
    return build_settlement_effect_plan_v1(
        ProposedSettlementEffectPlanV1(
            application_id=base.application_id,
            chain_or_domain_id=base.chain_or_domain_id,
            epoch_id=base.epoch_id,
            source_root_journal_hash=base.source_root_journal_hash,
            public_policy_hash=base.public_policy_hash,
            pre_state_root=base.pre_state_root,
            post_state_root=base.post_state_root,
            economic_action_ids=(*base.economic_action_ids, message_action_id),
            ledger_cell_writes=(*base.ledger_cell_writes, message_cell_write),
            asset_effects=asset_effects,
            authorization_consumptions=(
                *base.authorization_consumptions,
                reward_authorization,
            ),
            message_effects=(message,),
            carry_effects=(carry,),
            reward_effects=(reward,),
        )
    )


def _authenticated_root(
    plan: SettlementEffectPlanV1,
    *,
    request_byte: str = "33",
) -> _AuthenticatedRecursiveStarkRootFacts:
    facts = _facts(plan)
    policy = TrustedRecursiveStarkAdmissionPolicy(
        expected_chain_id=facts.chain_id,
        expected_epoch_id=facts.epoch_id,
        expected_proof_profile=facts.proof_profile,
        expected_verifier_set_root=facts.verifier_set_root,
        expected_public_policy_hash=facts.public_policy_hash,
    )
    provenance = _RecursiveStarkVerificationProvenance(
        authority_manifest_sha256="11" * 32,
        verifier_executable_sha256="22" * 32,
        verification_request_sha256=request_byte * 32,
        release_binding_config_digest="0x" + "44" * 32,
        replay_manifest_sha256="sha256:" + "55" * 32,
    )
    return _mint_recursive_stark_root_facts_after_verification(facts, policy, provenance)


def _sealed(
    plan: SettlementEffectPlanV1, *, request_byte: str = "33"
) -> _AuthenticatedSettlementCommitV1:
    return _mint_test_only_authenticated_settlement_commit_v1(
        _authenticated_root(plan, request_byte=request_byte),
        plan,
    )


def _mint_test_only_authenticated_settlement_commit_v1(
    authenticated_root: _AuthenticatedRecursiveStarkRootFacts,
    plan: SettlementEffectPlanV1,
) -> _AuthenticatedSettlementCommitV1:
    """Construct the sealed authority-false input only inside this test module."""

    return _AuthenticatedSettlementCommitV1(
        authenticated_root,
        plan,
        seal=settlement_authority_module._AUTHENTICATED_SETTLEMENT_COMMIT_SEAL_V1,
    )


def _store(
    tmp_path: Path, name: str = "zrpf-settlement.sqlite3"
) -> SQLiteZrpfAtomicSettlementStoreV1:
    return SQLiteZrpfAtomicSettlementStoreV1(
        tmp_path / name,
        genesis_settlement_state_root=_hash(3),
    )


def _commit(
    store: SQLiteZrpfAtomicSettlementStoreV1,
    sealed: _AuthenticatedSettlementCommitV1,
):
    return store._commit_authenticated_settlement(
        expected_admission_cursor=store.read_admission_cursor(),
        expected_settlement_cursor=store.read_settlement_cursor(),
        authenticated_settlement=sealed,
    )


_KERNEL_TABLES = (
    "zrpf_admissions",
    "zrpf_child_claims",
    "zrpf_accepted_receipts",
    "zrpf_cross_shard_messages",
    "zrpf_settlement_plans",
    "zrpf_settlement_economic_actions",
    "zrpf_settlement_cell_writes",
    "zrpf_settlement_asset_effects",
    "zrpf_settlement_authorization_consumptions",
    "zrpf_settlement_message_effects",
    "zrpf_settlement_carry_effects",
    "zrpf_settlement_reward_effects",
)


def _database_kernel_snapshot(path: Path) -> tuple[object, ...]:
    with sqlite3.connect(path) as connection:
        counts = tuple(
            int(connection.execute(f"SELECT count(*) FROM {table}").fetchone()[0])
            for table in _KERNEL_TABLES
        )
        replay_meta = connection.execute("SELECT * FROM zrpf_store_meta").fetchall()
        settlement_meta = connection.execute("SELECT * FROM zrpf_settlement_meta").fetchall()
    return counts, replay_meta, settlement_meta


def test_store_commits_replay_plan_and_all_rows_with_authority_false(tmp_path: Path) -> None:
    store = _store(tmp_path)
    plan = _plan_with_every_row_family()

    result = _commit(store, _sealed(plan))

    assert result.disposition is ZrpfAtomicSettlementDispositionV1.TRANSACTION_COMMITTED
    assert result.committed is True
    assert result.settlement_authority is False
    assert result.settlement_receipt is not None
    assert result.settlement_receipt.plan_commitment == plan.commitment
    assert result.settlement_receipt.authority_blocked_reason == (
        SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1
    )
    assert result.admission_head.revision == 1
    assert result.settlement_head.revision == 1
    assert result.settlement_head.state_root == plan.post_state_root
    with sqlite3.connect(store.path) as connection:
        assert connection.execute("PRAGMA application_id").fetchone()[0] == (
            ATOMIC_SETTLEMENT_STORE_APPLICATION_ID_V1
        )
        assert connection.execute("PRAGMA user_version").fetchone()[0] == (
            ATOMIC_SETTLEMENT_STORE_SCHEMA_VERSION_V1
        )
        expected_counts = {
            "zrpf_admissions": 1,
            "zrpf_settlement_plans": 1,
            "zrpf_settlement_economic_actions": 3,
            "zrpf_settlement_cell_writes": 3,
            "zrpf_settlement_asset_effects": 3,
            "zrpf_settlement_authorization_consumptions": 2,
            "zrpf_settlement_message_effects": 1,
            "zrpf_settlement_carry_effects": 1,
            "zrpf_settlement_reward_effects": 1,
        }
        for table, expected in expected_counts.items():
            assert connection.execute(f"SELECT count(*) FROM {table}").fetchone()[0] == expected


def test_production_binding_fails_closed() -> None:
    plan = _plan()
    root = _authenticated_root(plan)

    with pytest.raises(
        SettlementSemanticBindingUnavailableV1,
        match=SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1,
    ):
        _bind_authenticated_settlement_commit_v1(root, plan)


def test_no_public_commit_method_exists(tmp_path: Path) -> None:
    store = _store(tmp_path)

    assert not hasattr(store, "commit")
    assert not hasattr(store, "commit_settlement")
    assert store.settlement_authority is False
    assert store.read_admission_cursor().revision == 0


def test_invalid_public_receipt_lookup_is_a_stable_typed_store_error(tmp_path: Path) -> None:
    store = _store(tmp_path)

    with pytest.raises(
        ZrpfAtomicSettlementStoreErrorV1,
        match="ATOMIC_SETTLEMENT_RECEIPT_READ_FAILED",
    ) as caught:
        store.get_settlement_receipt("malformed")

    assert caught.value.code == "ATOMIC_SETTLEMENT_RECEIPT_READ_FAILED"
    assert store.read_admission_cursor().revision == 0


def test_forged_sealed_input_rejects_before_database_mutation(tmp_path: Path) -> None:
    store = _store(tmp_path)
    forged = object.__new__(_AuthenticatedSettlementCommitV1)

    with pytest.raises(TypeError, match="lacks the private seal"):
        store._commit_authenticated_settlement(
            expected_admission_cursor=store.read_admission_cursor(),
            expected_settlement_cursor=store.read_settlement_cursor(),
            authenticated_settlement=forged,
        )

    assert store.read_admission_cursor().revision == 0
    assert store.read_settlement_cursor().revision == 0


def test_exact_retry_is_idempotent_across_restart(tmp_path: Path) -> None:
    store = _store(tmp_path)
    plan = _plan()
    sealed = _sealed(plan)
    initial_admission = store.read_admission_cursor()
    initial_settlement = store.read_settlement_cursor()
    committed = store._commit_authenticated_settlement(
        expected_admission_cursor=initial_admission,
        expected_settlement_cursor=initial_settlement,
        authenticated_settlement=sealed,
    )

    restarted = _store(tmp_path)
    replay = restarted._commit_authenticated_settlement(
        expected_admission_cursor=initial_admission,
        expected_settlement_cursor=initial_settlement,
        authenticated_settlement=sealed,
    )

    assert committed.committed is True
    assert replay.idempotent_replay is True
    assert replay.admission_receipt == committed.admission_receipt
    assert replay.settlement_receipt == committed.settlement_receipt
    assert restarted.read_admission_cursor().revision == 1
    assert restarted.read_settlement_cursor().revision == 1


def test_lost_response_after_commit_recovers_by_fresh_seal_retry(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    store = _store(tmp_path)
    plan = _plan()
    first_seal = _sealed(plan)
    original = SQLiteZrpfAtomicSettlementStoreV1._committed_result

    def lose_response(*_args: object, **_kwargs: object) -> None:
        raise ValueError("injected response loss after commit")

    monkeypatch.setattr(SQLiteZrpfAtomicSettlementStoreV1, "_committed_result", lose_response)
    with pytest.raises(ZrpfAtomicSettlementStoreErrorV1, match="ATOMIC_SETTLEMENT_COMMIT_FAILED"):
        _commit(store, first_seal)
    monkeypatch.setattr(SQLiteZrpfAtomicSettlementStoreV1, "_committed_result", original)

    fresh_seal = _sealed(plan)
    replay = store._commit_authenticated_settlement(
        expected_admission_cursor=store.read_admission_cursor(),
        expected_settlement_cursor=store.read_settlement_cursor(),
        authenticated_settlement=fresh_seal,
    )
    assert fresh_seal is not first_seal
    assert replay.idempotent_replay is True
    assert replay.settlement_receipt == store.get_settlement_receipt(plan.commitment)


@pytest.mark.skipif(not hasattr(os, "fork"), reason="requires POSIX process-exit semantics")
def test_process_exit_after_commit_recovers_by_exact_retry(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    store = _store(tmp_path)
    plan = _plan()
    original = SQLiteZrpfAtomicSettlementStoreV1._committed_result

    def exit_after_commit(*_args: object, **_kwargs: object) -> None:
        os._exit(91)

    monkeypatch.setattr(
        SQLiteZrpfAtomicSettlementStoreV1,
        "_committed_result",
        exit_after_commit,
    )
    process_id = os.fork()
    if process_id == 0:
        _commit(store, _sealed(plan))
        os._exit(90)
    _, status = os.waitpid(process_id, 0)
    monkeypatch.setattr(SQLiteZrpfAtomicSettlementStoreV1, "_committed_result", original)

    assert os.waitstatus_to_exitcode(status) == 91
    restarted = _store(tmp_path)
    replay = _commit(restarted, _sealed(plan))
    assert replay.idempotent_replay is True
    assert restarted.read_admission_cursor().revision == 1
    assert restarted.read_settlement_cursor().revision == 1


def test_pre_state_mismatch_is_reject_is_noop(tmp_path: Path) -> None:
    store = _store(tmp_path)
    plan = _plan(pre_state=99)
    before = (store.read_admission_cursor(), store.read_settlement_cursor())

    result = _commit(store, _sealed(plan))

    assert result.settlement_reject_reason is (
        ZrpfAtomicSettlementRejectReasonV1.PRE_STATE_ROOT_MISMATCH
    )
    assert (store.read_admission_cursor(), store.read_settlement_cursor()) == before
    assert store.get_settlement_receipt(plan.commitment) is None


def test_settlement_cursor_mismatch_is_reject_is_noop(tmp_path: Path) -> None:
    store = _store(tmp_path)
    plan = _plan()
    before = (store.read_admission_cursor(), store.read_settlement_cursor())
    wrong_cursor = DurableZrpfSettlementCursorV1(
        revision=0,
        state_root=_hash(99),
        plan_count=0,
    )

    result = store._commit_authenticated_settlement(
        expected_admission_cursor=before[0],
        expected_settlement_cursor=wrong_cursor,
        authenticated_settlement=_sealed(plan),
    )

    assert result.settlement_reject_reason is (
        ZrpfAtomicSettlementRejectReasonV1.SETTLEMENT_CURSOR_MISMATCH
    )
    assert (store.read_admission_cursor(), store.read_settlement_cursor()) == before


def test_duplicate_economic_action_and_grant_spend_reject_without_mutation(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    first = _plan()
    assert _commit(store, _sealed(first)).committed
    before = (store.read_admission_cursor(), store.read_settlement_cursor())

    duplicate_action = _plan(
        root=31,
        epoch=10,
        pre_state=4,
        post_state=5,
        ordinary_action=10,
        authorized_action=13,
        grant=22,
        cell_base=70,
    )
    action_result = _commit(store, _sealed(duplicate_action, request_byte="66"))
    assert action_result.settlement_reject_reason is (
        ZrpfAtomicSettlementRejectReasonV1.DUPLICATE_ECONOMIC_ACTION
    )
    assert (store.read_admission_cursor(), store.read_settlement_cursor()) == before

    duplicate_grant = _plan(
        root=32,
        epoch=11,
        pre_state=4,
        post_state=6,
        ordinary_action=14,
        authorized_action=15,
        grant=21,
        cell_base=80,
    )
    grant_result = _commit(store, _sealed(duplicate_grant, request_byte="77"))
    assert grant_result.settlement_reject_reason is (
        ZrpfAtomicSettlementRejectReasonV1.DUPLICATE_AUTHORIZATION_GRANT_SPEND
    )
    assert (store.read_admission_cursor(), store.read_settlement_cursor()) == before


def test_two_writers_from_one_version_commit_exactly_once(tmp_path: Path) -> None:
    path = tmp_path / "writer-race.sqlite3"
    stores = (
        SQLiteZrpfAtomicSettlementStoreV1(path, genesis_settlement_state_root=_hash(3)),
        SQLiteZrpfAtomicSettlementStoreV1(path, genesis_settlement_state_root=_hash(3)),
    )
    initial_admission = stores[0].read_admission_cursor()
    initial_settlement = stores[0].read_settlement_cursor()
    plans = (
        _plan(root=30, ordinary_action=10, authorized_action=11, grant=21),
        _plan(
            root=31,
            epoch=10,
            ordinary_action=12,
            authorized_action=13,
            grant=22,
            cell_base=70,
        ),
    )
    sealed = (_sealed(plans[0], request_byte="66"), _sealed(plans[1], request_byte="77"))

    with ThreadPoolExecutor(max_workers=2) as pool:
        futures = [
            pool.submit(
                store._commit_authenticated_settlement,
                expected_admission_cursor=initial_admission,
                expected_settlement_cursor=initial_settlement,
                authenticated_settlement=value,
            )
            for store, value in zip(stores, sealed, strict=True)
        ]
    results = [future.result() for future in futures]

    assert sum(result.committed for result in results) == 1
    rejected = next(result for result in results if not result.committed)
    assert rejected.settlement_reject_reason is (
        ZrpfAtomicSettlementRejectReasonV1.ADMISSION_CURSOR_MISMATCH
    )
    assert stores[0].read_admission_cursor().revision == 1
    assert stores[0].read_settlement_cursor().revision == 1


@pytest.mark.parametrize(
    "stage",
    (
        "_persist_admission_rows",
        "_persist_settlement_header",
        "_persist_settlement_actions",
        "_persist_settlement_rows",
        "_cas_meta",
        "_cas_settlement_meta",
    ),
)
def test_failure_after_each_transaction_stage_rolls_back_every_row(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    stage: str,
) -> None:
    store = _store(tmp_path, f"rollback-{stage}.sqlite3")
    before = _database_kernel_snapshot(store.path)
    original: Callable[..., object] = getattr(settlement_store_module, stage)

    def fail_after_stage(*args: object, **kwargs: object) -> None:
        original(*args, **kwargs)
        raise sqlite3.OperationalError(f"injected failure after {stage}")

    monkeypatch.setattr(settlement_store_module, stage, fail_after_stage)
    with pytest.raises(ZrpfAtomicSettlementStoreErrorV1, match="ATOMIC_SETTLEMENT_COMMIT_FAILED"):
        _commit(store, _sealed(_plan()))
    monkeypatch.setattr(settlement_store_module, stage, original)

    restarted = _store(tmp_path, f"rollback-{stage}.sqlite3")
    assert restarted.read_admission_cursor().revision == 0
    assert restarted.read_settlement_cursor().revision == 0
    assert _database_kernel_snapshot(restarted.path) == before


@pytest.mark.parametrize(
    ("mutation", "match"),
    (
        (
            "UPDATE zrpf_settlement_plans "
            "SET canonical_plan = CAST(canonical_plan || x'20' AS BLOB)",
            "noncanonical",
        ),
        (
            f"UPDATE zrpf_settlement_meta SET state_root = x'{99:064x}' WHERE singleton = 1",
            "state root does not match history",
        ),
        (
            "UPDATE zrpf_settlement_cell_writes SET canonical_record = x'7b7d' WHERE ordinal = 0",
            "record mismatch",
        ),
    ),
)
def test_restart_rejects_plan_meta_and_row_tampering(
    tmp_path: Path,
    mutation: str,
    match: str,
) -> None:
    store = _store(tmp_path)
    assert _commit(store, _sealed(_plan())).committed
    with sqlite3.connect(store.path) as connection:
        connection.execute(mutation)

    with pytest.raises(ZrpfAtomicSettlementStoreErrorV1, match=match):
        _store(tmp_path)


def _erase_settlement_side_of_committed_history(path: Path) -> None:
    with sqlite3.connect(path) as connection:
        for table in reversed(_KERNEL_TABLES[4:]):
            connection.execute(f"DELETE FROM {table}")
        connection.execute(
            """
            UPDATE zrpf_settlement_meta
            SET revision = 0, plan_count = 0, state_root = ?
            WHERE singleton = 1
            """,
            (bytes.fromhex(_hash(3)[2:]),),
        )


def test_restart_rejects_admission_only_split_history(tmp_path: Path) -> None:
    store = _store(tmp_path)
    assert _commit(store, _sealed(_plan())).committed
    _erase_settlement_side_of_committed_history(store.path)

    with pytest.raises(
        ZrpfAtomicSettlementStoreErrorV1,
        match="admission and settlement history revisions diverge",
    ):
        _store(tmp_path)


def test_locked_commit_rejects_admission_only_split_history(tmp_path: Path) -> None:
    store = _store(tmp_path)
    assert _commit(store, _sealed(_plan())).committed
    _erase_settlement_side_of_committed_history(store.path)
    second = _plan(
        root=31,
        epoch=10,
        pre_state=3,
        post_state=5,
        ordinary_action=12,
        authorized_action=13,
        grant=22,
        cell_base=70,
    )

    with pytest.raises(
        ZrpfAtomicSettlementStoreErrorV1,
        match="admission and settlement history revisions diverge",
    ):
        _commit(store, _sealed(second, request_byte="66"))


def _canonical_test_json(value: object) -> bytes:
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"), sort_keys=True).encode()


def _add_unknown_plan_field(raw: bytes) -> bytes:
    value = json.loads(raw)
    assert type(value) is dict
    value["unknown_authority_field"] = True
    return _canonical_test_json(value)


def _tamper_derived_effect_id(raw: bytes) -> bytes:
    value = json.loads(raw)
    assert type(value) is dict
    effects = value["asset_effects"]
    assert type(effects) is list and effects
    assert type(effects[0]) is dict
    effects[0]["effect_id"] = _hash(999)
    return _canonical_test_json(value)


@pytest.mark.parametrize(
    ("mutate", "match"),
    (
        (_add_unknown_plan_field, "key set mismatch"),
        (_tamper_derived_effect_id, "typed V1 validation"),
        (lambda raw: raw.replace(b'"epoch_id":9', b'"epoch_id":9.5'), "invalid bounded JSON"),
        (lambda _raw: b"[" * 2_000 + b"0" + b"]" * 2_000, "nesting exceeds"),
    ),
)
def test_restart_normalizes_malformed_or_semantically_invalid_plan_bytes(
    tmp_path: Path,
    mutate: Callable[[bytes], bytes],
    match: str,
) -> None:
    store = _store(tmp_path)
    assert _commit(store, _sealed(_plan())).committed
    with sqlite3.connect(store.path) as connection:
        raw = bytes(
            connection.execute("SELECT canonical_plan FROM zrpf_settlement_plans").fetchone()[0]
        )
        connection.execute(
            "UPDATE zrpf_settlement_plans SET canonical_plan = ?",
            (mutate(raw),),
        )

    with pytest.raises(ZrpfAtomicSettlementStoreErrorV1, match=match) as caught:
        _store(tmp_path)
    assert caught.value.code == "ATOMIC_SETTLEMENT_STORE_OPEN_FAILED"


def test_schema_constraints_prevent_authority_or_blocked_reason_promotion(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    with sqlite3.connect(store.path) as connection:
        with pytest.raises(sqlite3.IntegrityError):
            connection.execute(
                "UPDATE zrpf_settlement_meta SET settlement_authority = 1 WHERE singleton = 1"
            )
        with pytest.raises(sqlite3.IntegrityError):
            connection.execute(
                "UPDATE zrpf_settlement_meta SET authority_blocked_reason = 'approved' "
                "WHERE singleton = 1"
            )


def test_state_machine_sequence_checks_invariants_after_every_action(tmp_path: Path) -> None:
    store = _store(tmp_path)
    first = _plan()
    second = _plan(
        root=31,
        epoch=10,
        pre_state=4,
        post_state=5,
        ordinary_action=12,
        authorized_action=13,
        grant=22,
        cell_base=70,
    )
    actions = (
        ("commit", _sealed(first, request_byte="61"), True, 1),
        ("replay", _sealed(first, request_byte="61"), True, 1),
        ("commit", _sealed(second, request_byte="62"), True, 2),
    )
    for name, value, accepted, expected_revision in actions:
        result = _commit(store, value)
        assert (result.committed or result.idempotent_replay) is accepted, name
        assert store.read_admission_cursor().revision == expected_revision, name
        assert store.read_settlement_cursor().revision == expected_revision, name
        restarted = SQLiteZrpfAtomicSettlementStoreV1(
            store.path,
            genesis_settlement_state_root=_hash(3),
        )
        assert restarted.read_admission_cursor() == store.read_admission_cursor(), name
        assert restarted.read_settlement_cursor() == store.read_settlement_cursor(), name


def test_test_mint_rejects_partial_root_plan_mismatch() -> None:
    plan = _plan()
    root = _authenticated_root(plan)
    mismatched = replace(plan, source_root_journal_hash=_hash(99))

    with pytest.raises(ValueError, match="source root"):
        _mint_test_only_authenticated_settlement_commit_v1(root, mismatched)


def test_test_only_settlement_mint_has_no_non_test_call_site() -> None:
    repository = Path(__file__).resolve().parents[2]
    needles = (
        "_AUTHENTICATED_SETTLEMENT_COMMIT_SEAL_V1",
        "_AuthenticatedSettlementCommitV1(",
    )
    allowed = {
        repository / "src/core/_zrpf_settlement_commit_authority.py",
        Path(__file__).resolve(),
    }
    offenders = []
    for path in repository.rglob("*.py"):
        if path in allowed:
            continue
        source = path.read_text(encoding="utf-8")
        if any(needle in source for needle in needles):
            offenders.append(path.relative_to(repository).as_posix())
    assert offenders == []
