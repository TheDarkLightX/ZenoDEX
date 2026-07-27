from __future__ import annotations

from dataclasses import fields, replace

import pytest

import src.core.fcis_decision_derivation as decision_derivation
import src.core.fcis_step_evaluator as step_evaluator
from src.core.batch_clearing import compute_settlement
from src.core.dex import DexState
from src.core.fcis_authority_admission import (
    CanonicalAuthorityClaimBytesV1,
    admit_fcis_authority_claim_v1,
    encode_fcis_authority_claim_v1,
)
from src.core.fcis_decision_derivation import (
    FCIS_SPOT_TRANSITION_BUDGET_V1,
    AcceptV1,
    CommittedFailureV1,
    RejectV1,
    acceptance_receipt_root_v1,
    evaluate_fcis_decision_v1,
)
from src.core.fcis_decision_values import (
    FCIS_COMMITTED_FAILURE_RECEIPT_SCHEMA_ID_V1,
    FCIS_REJECTION_RECEIPT_SCHEMA_ID_V1,
    CommittedFailureReceiptClaimV1,
    CommittedFailureReceiptSourceV1,
    FCISCommittedFailureCodeV1,
)
from src.core.fcis_step_evaluation_values import FCISStepEvaluationOkV1
from src.core.fcis_step_evaluator import evaluate_fcis_step_candidate_v1
from src.core.settlement_snapshots import snapshot_settlement
from src.state import BalanceTable, LPTable
from src.state.fcis_committed_state_values import FCISCommittedStateV1
from src.state.intent_snapshots import admit_intent_batch
from src.state.intents import Intent, IntentKind
from src.state.snapshot_combinators import AdmitOk
from src.state.state_transitions import (
    BalancePatchApplyOkV1,
    CanonicalBalancePatchV1,
    CanonicalNoncePatchV1,
    CanonicalPoolPatchV1,
    NoncePatchApplyOkV1,
    PoolPatchApplyOkV1,
    apply_canonical_balance_patch_v1,
    apply_canonical_nonce_patch_v1,
    apply_canonical_pool_patch_v1,
)
from tests.core.test_fcis_step_evaluator import (
    _context_source,
    _state_source,
    _swap_case,
)
from tests.core.test_fcis_support_profile_v5 import (
    SENDER,
    _iid,
)
from tests.core.test_fcis_support_profile_v5 import (
    _context_source as _support_context_source,
)
from tests.core.test_fcis_support_profile_v5 import (
    _state_source as _support_state_source,
)


def _exact_inputs() -> dict[str, object]:
    state, intent, settlement = _swap_case()
    return {
        "state_source": _state_source(state),
        "settlement": snapshot_settlement(settlement),
        "intents": admit_intent_batch([intent]),
        "context": _context_source(),
        "budget": FCIS_SPOT_TRANSITION_BUDGET_V1,
    }


def _two_event_inputs() -> dict[str, object]:
    """Build one replay-valid batch with exactly two canonical events."""

    assets = tuple("0x" + f"{index:02x}" * 32 for index in range(1, 5))
    balances = BalanceTable()
    for asset in assets:
        balances.set(SENDER, asset, 10_000_000)
    state = DexState(balances=balances, pools={}, lp_balances=LPTable())
    intents = tuple(
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.CREATE_POOL,
            intent_id=_iid(200 + index),
            sender_pubkey=SENDER,
            deadline=10_000,
            fields={
                "asset0": assets[index * 2],
                "asset1": assets[index * 2 + 1],
                "fee_bps": 30 + index,
                "amount0": 2_000_000,
                "amount1": 2_000_000,
                "nonce": index + 1,
            },
        )
        for index in range(2)
    )
    settlement = compute_settlement(
        list(intents),
        state.pools,
        state.balances,
        state.lp_balances,
        swap_ordering="greedy_ab_refined",
    )
    assert settlement.events is not None
    assert len(settlement.events) == 2
    return {
        "state_source": _support_state_source(state),
        "settlement": snapshot_settlement(settlement),
        "intents": admit_intent_batch(intents),
        "context": _support_context_source(),
        "budget": FCIS_SPOT_TRANSITION_BUDGET_V1,
    }


def _accept() -> AcceptV1:
    result = evaluate_fcis_decision_v1(**_exact_inputs())
    assert type(result) is AcceptV1
    return result


def _patch_write_count(accept: AcceptV1) -> int:
    patch = accept.commit_plan.patch
    return (
        len(patch.balance_writes)
        + len(patch.pool_writes)
        + len(patch.lp_writes)
        + sum(
            write is not None
            for write in (
                patch.fee_accumulator_write,
                patch.vault_write,
                patch.oracle_write,
                patch.perps_write,
            )
        )
        + len(accept.commit_plan.replay.nonce_advances)
    )


def test_accept_is_deterministic_and_reproduces_one_exact_successor() -> None:
    inputs = _exact_inputs()
    first = evaluate_fcis_decision_v1(**inputs)
    second = evaluate_fcis_decision_v1(**inputs)

    assert type(first) is AcceptV1
    assert first == second
    assert tuple(field.name for field in fields(first)) == (
        "next_state",
        "commit_plan",
        "receipt",
    )
    assert tuple(field.name for field in fields(first.next_state)) == (
        "balances",
        "pools",
        "lp_balances",
        "nonces",
        "vault",
        "oracle",
        "fee_accumulator",
        "perps",
    )

    plan = first.commit_plan
    binding = first.receipt.binding
    pre_state_source = inputs["state_source"]
    evaluation = evaluate_fcis_step_candidate_v1(
        state_source=pre_state_source,
        settlement=inputs["settlement"],
        intents=inputs["intents"],
        context=inputs["context"],
    )
    assert type(evaluation) is FCISStepEvaluationOkV1
    pre_state = evaluation.material.pre_state

    balances = apply_canonical_balance_patch_v1(
        pre_state.balances,
        CanonicalBalancePatchV1(plan.patch.balance_writes),
    )
    pools = apply_canonical_pool_patch_v1(
        pre_state.pools,
        CanonicalPoolPatchV1(plan.patch.pool_writes),
    )
    nonces = apply_canonical_nonce_patch_v1(
        pre_state.nonces,
        CanonicalNoncePatchV1(plan.replay.nonce_advances),
    )
    assert type(balances) is BalancePatchApplyOkV1
    assert type(pools) is PoolPatchApplyOkV1
    assert plan.patch.lp_writes == ()
    assert type(nonces) is NoncePatchApplyOkV1
    assert balances.state == first.next_state.balances
    assert pools.state == first.next_state.pools
    assert pre_state.lp_balances == first.next_state.lp_balances
    assert nonces.state == first.next_state.nonces
    assert plan.patch.fee_accumulator_write is not None
    assert plan.patch.fee_accumulator_write.expected == pre_state.fee_accumulator
    assert plan.patch.fee_accumulator_write.replacement == first.next_state.fee_accumulator
    assert binding.next_state_root == binding.snapshot_commitment
    assert binding.pre_state_root == evaluation.evidence.pre_state_root
    assert acceptance_receipt_root_v1(first) == acceptance_receipt_root_v1(second)


def test_authoritative_decision_constructors_are_controlled() -> None:
    """M5-P3-BUNDLE-010: reserved failure is typed but has no production rule."""
    accept = _accept()
    with pytest.raises(TypeError, match="controlled derivation"):
        AcceptV1(accept.next_state, accept.commit_plan, accept.receipt, object())

    inputs = _exact_inputs()
    rejection = evaluate_fcis_decision_v1(
        **{**inputs, "settlement": object()},
    )
    assert type(rejection) is RejectV1
    with pytest.raises(TypeError, match="controlled derivation"):
        RejectV1(rejection.receipt, object())
    source = CommittedFailureReceiptSourceV1(
        binding=accept.receipt.binding,
        failure_code=FCISCommittedFailureCodeV1.RESERVED_UNMOUNTED,
    )
    admitted = admit_fcis_authority_claim_v1(
        FCIS_COMMITTED_FAILURE_RECEIPT_SCHEMA_ID_V1,
        source,
    )
    assert type(admitted) is AdmitOk
    assert type(admitted.value) is CommittedFailureReceiptClaimV1
    with pytest.raises(TypeError, match="controlled derivation"):
        CommittedFailureV1(
            accept.next_state,
            accept.commit_plan,
            admitted.value,
            object(),
        )


@pytest.mark.parametrize(
    "mutate",
    (
        lambda inputs: {**inputs, "settlement": object()},
        lambda inputs: {
            **inputs,
            "state_source": replace(inputs["state_source"], pools=[]),
        },
        lambda inputs: {
            **inputs,
            "context": replace(inputs["context"], require_all_nonces=1),
        },
    ),
)
def test_each_early_rejection_is_only_one_canonical_receipt(mutate) -> None:
    result = evaluate_fcis_decision_v1(**mutate(_exact_inputs()))

    assert type(result) is RejectV1
    assert tuple(field.name for field in fields(result)) == ("receipt",)
    for forbidden in (
        "next_state",
        "commit_plan",
        "effects",
        "replay",
        "outbox",
        "candidate",
        "evidence",
    ):
        assert not hasattr(result, forbidden)
    encoded = encode_fcis_authority_claim_v1(
        FCIS_REJECTION_RECEIPT_SCHEMA_ID_V1,
        result.receipt,
    )
    assert type(encoded) is CanonicalAuthorityClaimBytesV1


def test_canonical_command_is_admitted_exactly_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls = 0
    original = step_evaluator._admit_exact_command_v1

    def counted(settlement: object, intents: object):
        nonlocal calls
        calls += 1
        return original(settlement, intents)

    monkeypatch.setattr(step_evaluator, "_admit_exact_command_v1", counted)

    result = evaluate_fcis_decision_v1(**_exact_inputs())

    assert type(result) is AcceptV1
    assert calls == 1


def test_post_evaluation_substitution_fails_to_a_receipt_only_reject(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    inputs = _exact_inputs()
    evaluation = evaluate_fcis_step_candidate_v1(
        state_source=inputs["state_source"],
        settlement=inputs["settlement"],
        intents=inputs["intents"],
        context=inputs["context"],
    )
    assert type(evaluation) is FCISStepEvaluationOkV1
    object.__setattr__(evaluation.evidence, "post_state_root", "0x" + "00" * 32)
    monkeypatch.setattr(
        decision_derivation,
        "_evaluate_fcis_step_candidate_bound_v1",
        lambda **_kwargs: evaluation,
    )

    result = evaluate_fcis_decision_v1(**inputs)

    assert type(result) is RejectV1
    assert tuple(field.name for field in fields(result)) == ("receipt",)
    assert not hasattr(result, "candidate")


def test_patch_budget_accepts_at_bound_and_rejects_one_below() -> None:
    baseline = _accept()
    observed = _patch_write_count(baseline)
    assert observed > 1
    inputs = _exact_inputs()

    at_bound = evaluate_fcis_decision_v1(
        **{
            **inputs,
            "budget": replace(
                FCIS_SPOT_TRANSITION_BUDGET_V1,
                max_patch_writes=observed,
            ),
        }
    )
    one_below = evaluate_fcis_decision_v1(
        **{
            **inputs,
            "budget": replace(
                FCIS_SPOT_TRANSITION_BUDGET_V1,
                max_patch_writes=observed - 1,
            ),
        }
    )

    assert type(at_bound) is AcceptV1
    assert type(one_below) is RejectV1
    assert one_below.receipt.public_reason == ("transition budget exceeded: max_patch_writes")


def test_invalid_budget_rejects_before_step_evaluation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden_evaluation(**_kwargs: object) -> object:
        raise AssertionError("step evaluation ran before budget admission")

    monkeypatch.setattr(
        decision_derivation,
        "_evaluate_fcis_step_candidate_bound_v1",
        forbidden_evaluation,
    )
    inputs = _exact_inputs()
    result = evaluate_fcis_decision_v1(**{**inputs, "budget": object()})

    assert type(result) is RejectV1
    assert result.receipt.command_or_batch_root is None
    assert result.receipt.execution_context_hash is None
    assert result.receipt.pre_state_root is None


def test_accept_retains_only_exact_owned_values_after_source_mutation() -> None:
    inputs = _exact_inputs()
    result = evaluate_fcis_decision_v1(**inputs)
    assert type(result) is AcceptV1
    before = acceptance_receipt_root_v1(result)

    context = inputs["context"]
    object.__setattr__(context.settlement, "now", 999_999)

    assert type(result.next_state) is FCISCommittedStateV1
    assert acceptance_receipt_root_v1(result) == before


def test_outbox_budget_accepts_exactly_at_the_observed_count() -> None:
    """M5-P3-BUDGET-001: the exact outbox bound is accepted."""

    inputs = _two_event_inputs()
    result = evaluate_fcis_decision_v1(
        **{
            **inputs,
            "budget": replace(
                FCIS_SPOT_TRANSITION_BUDGET_V1,
                max_outbox_records=2,
            ),
        }
    )

    assert type(result) is AcceptV1


def test_outbox_budget_rejects_one_record_over_before_bundle_derivation() -> None:
    """M5-P3-BUDGET-002: one over the outbox bound is a typed rejection."""

    inputs = _two_event_inputs()
    result = evaluate_fcis_decision_v1(
        **{
            **inputs,
            "budget": replace(
                FCIS_SPOT_TRANSITION_BUDGET_V1,
                max_outbox_records=1,
            ),
        }
    )

    assert type(result) is RejectV1
    assert result.receipt.public_reason == "transition budget exceeded: max_outbox_records"
