from __future__ import annotations

from dataclasses import dataclass, fields, replace
from typing import cast

import pytest

from src.core.dex import DexState
from src.core.fcis_authority_admission import (
    CanonicalAuthorityClaimBytesV1,
    admit_fcis_authority_claim_v1,
    encode_fcis_authority_claim_v1,
)
from src.core.fcis_authority_schema import FCIS_AUTHORITY_RECORD_REGISTRATIONS_V1
from src.core.fcis_commit_bundle_values import (
    FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1,
    FCIS_COMMIT_BUNDLE_SCHEMA_ID_V2,
    CommitBundleClaimV1,
    CommitBundleClaimV2,
    CommitBundleSourceV1,
    CommitBundleSourceV2,
)
from src.core.fcis_decision_values import (
    FCIS_ACCEPTANCE_RECEIPT_SCHEMA_ID_V1,
    FCIS_COMMITTED_FAILURE_RECEIPT_SCHEMA_ID_V1,
    FCIS_DECISION_SCHEMA_ID_V1,
    FCIS_REJECTION_RECEIPT_SCHEMA_ID_V1,
    AcceptanceReceiptSourceV1,
    AcceptClaimV1,
    AcceptSourceV1,
    CommittedFailureClaimV1,
    CommittedFailureReceiptSourceV1,
    CommittedFailureSourceV1,
    FCISCommittedFailureCodeV1,
    FCISRejectCodeV1,
    ReceiptBindingSourceV1,
    RejectClaimV1,
    RejectionPathIndexPartSourceV1,
    RejectionPathTextPartSourceV1,
    RejectionReceiptSourceV1,
    RejectSourceV1,
)
from src.core.fcis_m6_profile_ids import ANF_VERSION_V1
from src.core.fcis_outbox_values import (
    FCIS_OUTBOX_PLAN_SCHEMA_ID_V1,
    FCIS_OUTBOX_PLAN_SCHEMA_ID_V2,
    OutboxEffectKindV1,
    OutboxPlanSourceV1,
    OutboxPlanSourceV2,
    OutboxPlanV1,
    OutboxPlanV2,
    OutboxRecordSourceV1,
)
from src.core.fcis_step_evaluation_values import FCISStepEvaluationPhaseV1
from src.core.fcis_transition_budget import (
    FCIS_TRANSITION_BUDGET_SCHEMA_ID_V1,
    TransitionBudgetSourceV1,
    TransitionBudgetV1,
)
from src.core.fcis_transition_values import (
    FCIS_COMMIT_PLAN_SCHEMA_ID_V1,
    FCIS_DEX_PATCH_SCHEMA_ID_V1,
    FCIS_EFFECTS_SCHEMA_ID_V1,
    FCIS_REPLAY_UPDATE_SCHEMA_ID_V1,
    BalanceWriteSourceV1,
    CanonicalDexPatchSourceV1,
    CanonicalDexPatchV1,
    CommitPlanSourceV1,
    FCISFeeAllocationSourceV1,
    FeeAccumulatorWriteSourceV1,
    LPPositionValueSourceV1,
    LPPositionWriteSourceV1,
    NonceAdvanceSourceV1,
    NullifierRecordSourceV1,
    OracleWriteSourceV1,
    OwnedDexEffectsSourceV1,
    PerpsWriteSourceV1,
    PoolWriteSourceV1,
    ReplayUpdateSourceV1,
    VaultWriteSourceV1,
)
from src.core.fees import FeeAccumulatorState
from src.core.oracle import OracleState
from src.core.perps import PERPS_STATE_VERSION_V4, PerpsState
from src.core.settlement import Settlement
from src.core.settlement_snapshots import snapshot_settlement
from src.core.vault import VaultState
from src.state import BalanceTable, LPTable
from src.state.fcis_committed_state_admission import admit_fcis_committed_state_v1
from src.state.fcis_committed_state_values import (
    FCISCommittedStateSourceV1,
    FCISCommittedStateV1,
)
from src.state.legacy_state_snapshots import (
    admit_legacy_balance_for_differential_v1,
    admit_legacy_lp_for_differential_v1,
    admit_legacy_nonce_for_differential_v1,
    admit_legacy_pool_map_for_differential_v1,
)
from src.state.pools import PoolState, PoolStatus, compute_pool_id
from src.state.snapshot_combinators import AdmitCode, AdmitOk, AdmitReject
from src.state.state_snapshots import (
    snapshot_fee_accumulator,
    snapshot_oracle,
    snapshot_perps,
    snapshot_pool,
    snapshot_vault,
)

_DIGEST = "0x" + "11" * 32
_OTHER_DIGEST = "0x" + "22" * 32
_PUBKEY = "0x" + "33" * 48
_INTENT_ID = "0x" + "44" * 32


def _owned_state() -> FCISCommittedStateV1:
    legacy = DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
    )
    source = FCISCommittedStateSourceV1(
        balances=admit_legacy_balance_for_differential_v1(legacy.balances),
        pools=admit_legacy_pool_map_for_differential_v1(legacy.pools),
        lp_balances=admit_legacy_lp_for_differential_v1(legacy.lp_balances),
        nonces=admit_legacy_nonce_for_differential_v1(legacy.nonces),
        vault=snapshot_vault(legacy.vault),
        oracle=snapshot_oracle(legacy.oracle),
        fee_accumulator=snapshot_fee_accumulator(legacy.fee_accumulator),
        perps=snapshot_perps(legacy.perps),
    )
    admitted = admit_fcis_committed_state_v1(source)
    assert type(admitted) is AdmitOk
    return cast(FCISCommittedStateV1, admitted.value)


def _owned_settlement():
    return snapshot_settlement(
        Settlement(
            module="TauSwap",
            version="0.1",
            batch_ref="batch-1",
            included_intents=[],
            fills=[],
            balance_deltas=[],
            reserve_deltas=[],
            lp_deltas=[],
            events=None,
        )
    )


def _binding_source() -> ReceiptBindingSourceV1:
    return ReceiptBindingSourceV1(
        algorithm_id="zenodex-fcis-spot",
        algorithm_version=1,
        schema_version=1,
        codec_version=1,
        execution_context_hash=_DIGEST,
        command_or_batch_root=_OTHER_DIGEST,
        budget_hash=_DIGEST,
        pre_state_root=_DIGEST,
        next_state_root=_OTHER_DIGEST,
        support_root_version=5,
        support_root=_DIGEST,
        support_set_commitment=_OTHER_DIGEST,
        snapshot_version=4,
        snapshot_commitment=_DIGEST,
        patch_root=_OTHER_DIGEST,
        commit_plan_root=_DIGEST,
    )


def _admit(schema_id: str, source: object) -> object:
    result = admit_fcis_authority_claim_v1(schema_id, source)
    assert type(result) is AdmitOk, result
    return result.value


def _sources() -> dict[str, object]:
    state = _owned_state()
    budget = TransitionBudgetSourceV1(
        max_canonical_input_bytes=1_000_000,
        max_depth=64,
        max_nodes=10_000,
        max_intents=256,
        max_state_reads=10_000,
        max_context_reads=128,
        max_patch_writes=10_000,
        max_effects=10_000,
        max_outbox_records=128,
        max_candidates=256,
        max_witness_bytes=1_000_000,
        max_receipt_bytes=1_000_000,
        max_integer_bits=256,
    )
    asset0 = "0x" + "55" * 32
    asset1 = "0x" + "66" * 32
    pool = snapshot_pool(
        PoolState(
            pool_id=compute_pool_id(asset0, asset1, 30),
            asset0=asset0,
            asset1=asset1,
            reserve0=100,
            reserve1=200,
            fee_bps=30,
            lp_supply=50,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
    )
    vault = snapshot_vault(VaultState(0, 0, 0, 0, 0))
    oracle = snapshot_oracle(OracleState(0, 300))
    perps = snapshot_perps(PerpsState(PERPS_STATE_VERSION_V4, {}))
    assert vault is not None and oracle is not None and perps is not None
    patch = CanonicalDexPatchSourceV1(
        (BalanceWriteSourceV1(("alice", "asset"), 0, 1),),
        (PoolWriteSourceV1(pool.pool_id, None, pool),),
        (
            LPPositionWriteSourceV1(
                ("provider", pool.pool_id),
                LPPositionValueSourceV1(0, None, None, 0, None),
                LPPositionValueSourceV1(1, 0, None, 0, 0),
            ),
        ),
        FeeAccumulatorWriteSourceV1(
            snapshot_fee_accumulator(FeeAccumulatorState(0)),
            snapshot_fee_accumulator(FeeAccumulatorState(1)),
        ),
        VaultWriteSourceV1(None, vault),
        OracleWriteSourceV1(None, oracle),
        PerpsWriteSourceV1(None, perps),
    )
    effects = OwnedDexEffectsSourceV1(
        _owned_settlement(),
        0,
        FCISFeeAllocationSourceV1(0, 0, 0, 0),
    )
    replay = ReplayUpdateSourceV1(
        (NonceAdvanceSourceV1(_PUBKEY, 0, 1),),
        (NullifierRecordSourceV1(_PUBKEY, _INTENT_ID),),
    )
    plan = CommitPlanSourceV1(patch, effects, replay)
    acceptance_receipt = AcceptanceReceiptSourceV1(_binding_source())
    rejection_receipt = RejectionReceiptSourceV1(
        algorithm_id="zenodex-fcis-spot",
        algorithm_version=1,
        schema_version=1,
        codec_version=1,
        command_or_batch_root=_OTHER_DIGEST,
        budget_hash=_DIGEST,
        execution_context_hash=None,
        pre_state_root=None,
        phase=FCISStepEvaluationPhaseV1.COMMAND_ADMISSION,
        code=FCISRejectCodeV1.WRONG_EXACT_TYPE,
        path=(
            RejectionPathTextPartSourceV1("commands"),
            RejectionPathIndexPartSourceV1(0),
        ),
        public_reason="command rejected",
    )
    committed_failure_receipt = CommittedFailureReceiptSourceV1(
        _binding_source(), FCISCommittedFailureCodeV1.RESERVED_UNMOUNTED
    )
    accept = AcceptSourceV1(state, plan, acceptance_receipt)
    outbox = OutboxPlanSourceV1(
        (
            OutboxRecordSourceV1(
                effect_index=0,
                effect_kind=OutboxEffectKindV1.CANONICAL_EVENT,
                effect_identity=_DIGEST,
                payload={"kind": "transition"},
                idempotency_key=_OTHER_DIGEST,
            ),
        )
    )
    anf_binding = replace(
        _binding_source(),
        authority_normal_form_version=ANF_VERSION_V1,
        authority_normal_form_root=_DIGEST,
    )
    anf_accept = AcceptSourceV1(state, plan, AcceptanceReceiptSourceV1(anf_binding))
    anf_outbox = OutboxPlanSourceV2(outbox.records, _DIGEST)
    return {
        FCIS_TRANSITION_BUDGET_SCHEMA_ID_V1: budget,
        FCIS_DEX_PATCH_SCHEMA_ID_V1: patch,
        FCIS_EFFECTS_SCHEMA_ID_V1: effects,
        FCIS_REPLAY_UPDATE_SCHEMA_ID_V1: replay,
        FCIS_COMMIT_PLAN_SCHEMA_ID_V1: plan,
        FCIS_ACCEPTANCE_RECEIPT_SCHEMA_ID_V1: acceptance_receipt,
        FCIS_REJECTION_RECEIPT_SCHEMA_ID_V1: rejection_receipt,
        FCIS_COMMITTED_FAILURE_RECEIPT_SCHEMA_ID_V1: committed_failure_receipt,
        FCIS_DECISION_SCHEMA_ID_V1: accept,
        FCIS_OUTBOX_PLAN_SCHEMA_ID_V1: outbox,
        FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1: CommitBundleSourceV1(
            expected_pre_root=_DIGEST,
            decision=accept,
            receipt_root=_OTHER_DIGEST,
            outbox_plan=outbox,
        ),
        FCIS_OUTBOX_PLAN_SCHEMA_ID_V2: anf_outbox,
        FCIS_COMMIT_BUNDLE_SCHEMA_ID_V2: CommitBundleSourceV2(
            expected_pre_root=_DIGEST,
            decision=anf_accept,
            receipt_root=_OTHER_DIGEST,
            outbox_plan=anf_outbox,
            authority_normal_form_root=_DIGEST,
        ),
    }


def test_every_m5_top_level_schema_admits_reconstructs_and_encodes() -> None:
    sources = _sources()
    assert len(sources) == 13
    for schema_id, source in sources.items():
        owned = _admit(schema_id, source)
        first = encode_fcis_authority_claim_v1(schema_id, source)
        second = encode_fcis_authority_claim_v1(schema_id, owned)
        assert type(first) is CanonicalAuthorityClaimBytesV1
        assert type(second) is CanonicalAuthorityClaimBytesV1
        assert first.payload == second.payload
        readmitted = _admit(schema_id, owned)
        assert readmitted == owned
        assert readmitted is not owned


def _collect_registered_record_types(
    value: object,
    registered_types: frozenset[type[object]],
    observed: set[type[object]],
) -> None:
    value_type = type(value)
    if value_type is tuple:
        for item in cast(tuple[object, ...], value):
            _collect_registered_record_types(item, registered_types, observed)
        return
    if value_type not in registered_types:
        return
    observed.add(value_type)
    for field in fields(value):
        _collect_registered_record_types(
            object.__getattribute__(value, field.name),
            registered_types,
            observed,
        )


def test_every_registered_m5_constructor_and_projector_is_exercised() -> None:
    sources = _sources()
    owned_values = [_admit(schema_id, source) for schema_id, source in sources.items()]
    owned_values.append(
        _admit(
            FCIS_DECISION_SCHEMA_ID_V1,
            RejectSourceV1(sources[FCIS_REJECTION_RECEIPT_SCHEMA_ID_V1]),
        )
    )
    owned_values.append(
        _admit(
            FCIS_DECISION_SCHEMA_ID_V1,
            CommittedFailureSourceV1(
                _owned_state(),
                sources[FCIS_COMMIT_PLAN_SCHEMA_ID_V1],
                sources[FCIS_COMMITTED_FAILURE_RECEIPT_SCHEMA_ID_V1],
            ),
        )
    )
    registered_types = frozenset(
        registration.owned_type for registration in FCIS_AUTHORITY_RECORD_REGISTRATIONS_V1
    )
    observed: set[type[object]] = set()
    for value in owned_values:
        _collect_registered_record_types(value, registered_types, observed)
    assert observed == registered_types, sorted(
        registered_type.__name__ for registered_type in registered_types - observed
    )


def test_canonical_claim_byte_evidence_requires_the_controlled_encoder() -> None:
    with pytest.raises(TypeError, match="controlled encoder"):
        CanonicalAuthorityClaimBytesV1(
            FCIS_DECISION_SCHEMA_ID_V1,
            b"{}",
            object(),
        )


def test_three_way_decision_claim_is_closed_and_reject_is_receipt_only() -> None:
    sources = _sources()
    accept = _admit(FCIS_DECISION_SCHEMA_ID_V1, sources[FCIS_DECISION_SCHEMA_ID_V1])
    reject_source = RejectSourceV1(sources[FCIS_REJECTION_RECEIPT_SCHEMA_ID_V1])
    committed_source = CommittedFailureSourceV1(
        _owned_state(),
        sources[FCIS_COMMIT_PLAN_SCHEMA_ID_V1],
        sources[FCIS_COMMITTED_FAILURE_RECEIPT_SCHEMA_ID_V1],
    )
    reject = _admit(FCIS_DECISION_SCHEMA_ID_V1, reject_source)
    committed = _admit(FCIS_DECISION_SCHEMA_ID_V1, committed_source)

    assert type(accept) is AcceptClaimV1
    assert type(reject) is RejectClaimV1
    assert tuple(field.name for field in fields(reject)) == ("receipt",)
    assert not hasattr(reject, "next_state")
    assert not hasattr(reject, "commit_plan")
    assert not hasattr(reject, "outbox_plan")
    assert type(committed) is CommittedFailureClaimV1

    @dataclass(frozen=True, slots=True)
    class UnknownDecisionSourceV1:
        receipt: object

    unknown = admit_fcis_authority_claim_v1(
        FCIS_DECISION_SCHEMA_ID_V1,
        UnknownDecisionSourceV1(sources[FCIS_REJECTION_RECEIPT_SCHEMA_ID_V1]),
    )
    assert type(unknown) is AdmitReject
    assert unknown.code is AdmitCode.WRONG_EXACT_TYPE


def test_reject_cannot_enter_a_commit_bundle() -> None:
    sources = _sources()
    source = CommitBundleSourceV1(
        expected_pre_root=_DIGEST,
        decision=RejectSourceV1(sources[FCIS_REJECTION_RECEIPT_SCHEMA_ID_V1]),
        receipt_root=_OTHER_DIGEST,
        outbox_plan=OutboxPlanSourceV1(()),
    )
    rejected = admit_fcis_authority_claim_v1(FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1, source)
    assert type(rejected) is AdmitReject
    assert rejected.code is AdmitCode.WRONG_EXACT_TYPE
    assert rejected.path == ("decision",)


def test_already_owned_corruption_is_rejected_without_partial_value() -> None:
    budget = cast(
        TransitionBudgetV1,
        _admit(
            FCIS_TRANSITION_BUDGET_SCHEMA_ID_V1,
            _sources()[FCIS_TRANSITION_BUDGET_SCHEMA_ID_V1],
        ),
    )
    object.__setattr__(budget, "max_depth", "hostile")
    rejected = admit_fcis_authority_claim_v1(FCIS_TRANSITION_BUDGET_SCHEMA_ID_V1, budget)
    assert type(rejected) is AdmitReject
    assert rejected.code is AdmitCode.WRONG_EXACT_TYPE
    assert rejected.path == ("max_depth",)
    assert not hasattr(rejected, "value")


def test_exact_source_types_reject_lookalikes() -> None:
    source = cast(
        TransitionBudgetSourceV1,
        _sources()[FCIS_TRANSITION_BUDGET_SCHEMA_ID_V1],
    )

    @dataclass(frozen=True, slots=True)
    class Lookalike:
        max_canonical_input_bytes: object
        max_depth: object
        max_nodes: object
        max_intents: object
        max_state_reads: object
        max_context_reads: object
        max_patch_writes: object
        max_effects: object
        max_outbox_records: object
        max_candidates: object
        max_witness_bytes: object
        max_receipt_bytes: object
        max_integer_bits: object

    rejected = admit_fcis_authority_claim_v1(
        FCIS_TRANSITION_BUDGET_SCHEMA_ID_V1,
        Lookalike(
            source.max_canonical_input_bytes,
            source.max_depth,
            source.max_nodes,
            source.max_intents,
            source.max_state_reads,
            source.max_context_reads,
            source.max_patch_writes,
            source.max_effects,
            source.max_outbox_records,
            source.max_candidates,
            source.max_witness_bytes,
            source.max_receipt_bytes,
            source.max_integer_bits,
        ),
    )
    assert type(rejected) is AdmitReject
    assert rejected.code is AdmitCode.WRONG_EXACT_TYPE
    assert rejected.path == ()


def test_patch_no_ops_fail_at_direct_and_closed_construction() -> None:
    from src.state.state_transitions import BalanceWriteV1

    no_op = BalanceWriteV1(("alice", "asset"), 0, None)
    with pytest.raises(ValueError, match="no-op"):
        CanonicalDexPatchV1((no_op,), (), (), None, None, None, None)

    rejected = admit_fcis_authority_claim_v1(
        FCIS_DEX_PATCH_SCHEMA_ID_V1,
        CanonicalDexPatchSourceV1((no_op,), (), (), None, None, None, None),
    )
    assert type(rejected) is AdmitReject
    assert rejected.code is AdmitCode.DOMAIN_INVARIANT


def test_outbox_indices_and_idempotency_keys_are_canonical() -> None:
    sources = _sources()
    owned = _admit(FCIS_OUTBOX_PLAN_SCHEMA_ID_V1, sources[FCIS_OUTBOX_PLAN_SCHEMA_ID_V1])
    assert type(owned) is OutboxPlanV1
    duplicate = OutboxPlanSourceV1(
        (
            OutboxRecordSourceV1(
                0,
                OutboxEffectKindV1.CANONICAL_EVENT,
                _DIGEST,
                {},
                _OTHER_DIGEST,
            ),
            OutboxRecordSourceV1(
                1,
                OutboxEffectKindV1.INDEX_REFRESH,
                _OTHER_DIGEST,
                {},
                _OTHER_DIGEST,
            ),
        )
    )
    rejected = admit_fcis_authority_claim_v1(FCIS_OUTBOX_PLAN_SCHEMA_ID_V1, duplicate)
    assert type(rejected) is AdmitReject
    assert rejected.code is AdmitCode.DOMAIN_INVARIANT


def test_legacy_commit_bundle_claim_preserves_exact_v1_field_surface() -> None:
    bundle = _admit(
        FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1,
        _sources()[FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1],
    )
    assert type(bundle) is CommitBundleClaimV1
    assert tuple(field.name for field in fields(bundle)) == (
        "expected_pre_root",
        "decision",
        "receipt_root",
        "outbox_plan",
    )
    assert bundle.next_state is bundle.decision.next_state
    assert bundle.commit_plan is bundle.decision.commit_plan
    assert bundle.receipt is bundle.decision.receipt


def test_legacy_v1_bundle_rejects_anf_bound_decision() -> None:
    """D04: ANF-bound decisions cannot cross the legacy bundle schema."""

    sources = _sources()
    legacy = cast(
        CommitBundleSourceV1,
        sources[FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1],
    )
    anf = cast(
        CommitBundleSourceV2,
        sources[FCIS_COMMIT_BUNDLE_SCHEMA_ID_V2],
    )

    rejected = admit_fcis_authority_claim_v1(
        FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1,
        replace(legacy, decision=anf.decision),
    )

    assert type(rejected) is AdmitReject
    assert rejected.code is AdmitCode.DOMAIN_INVARIANT
    assert rejected.path == ()


def test_anf_bound_commit_bundle_claim_uses_required_v2_root() -> None:
    bundle = _admit(
        FCIS_COMMIT_BUNDLE_SCHEMA_ID_V2,
        _sources()[FCIS_COMMIT_BUNDLE_SCHEMA_ID_V2],
    )

    assert type(bundle) is CommitBundleClaimV2
    assert type(bundle.outbox_plan) is OutboxPlanV2
    assert bundle.authority_normal_form_root == _DIGEST
    assert bundle.outbox_plan.authority_normal_form_root == _DIGEST
    assert bundle.receipt.binding.authority_normal_form_root == _DIGEST


def test_anf_bound_v2_outbox_rejects_missing_root() -> None:
    source = cast(
        OutboxPlanSourceV2,
        _sources()[FCIS_OUTBOX_PLAN_SCHEMA_ID_V2],
    )

    rejected = admit_fcis_authority_claim_v1(
        FCIS_OUTBOX_PLAN_SCHEMA_ID_V2,
        replace(source, authority_normal_form_root=None),
    )

    assert type(rejected) is AdmitReject
    assert rejected.code is AdmitCode.WRONG_EXACT_TYPE
    assert rejected.path == ("authority_normal_form_root",)


def test_anf_bound_v2_bundle_rejects_crossed_outer_root() -> None:
    source = cast(
        CommitBundleSourceV2,
        _sources()[FCIS_COMMIT_BUNDLE_SCHEMA_ID_V2],
    )

    rejected = admit_fcis_authority_claim_v1(
        FCIS_COMMIT_BUNDLE_SCHEMA_ID_V2,
        replace(source, authority_normal_form_root=_OTHER_DIGEST),
    )

    assert type(rejected) is AdmitReject
    assert rejected.code is AdmitCode.DOMAIN_INVARIANT
