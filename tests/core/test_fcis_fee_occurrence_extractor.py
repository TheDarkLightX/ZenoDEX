from __future__ import annotations

from dataclasses import replace
from inspect import signature

from src.core.batch_clearing import compute_settlement
from src.core.fcis_fee_occurrence_extractor import (
    PROTOCOL_FEE_DISTRIBUTION_DOMAIN_ID_V1,
    SourceBoundFeeOccurrenceCodeV1,
    SourceBoundFeeOccurrenceRejectV1,
    SourceBoundFeeOccurrenceV1,
    extract_source_bound_fee_occurrence_v1,
    verify_source_bound_fee_occurrence_v1,
)
from src.core.settlement_snapshots import snapshot_settlement
from src.state.fcis_execution_context_values import FCISFeeSplitPolicySourceV1
from src.state.intent_snapshots import admit_intent_batch, owned_intent_field_v1
from src.state.intents import Intent, IntentKind
from tests.core.test_fcis_decision_derivation import _exact_inputs
from tests.core.test_fcis_step_evaluator import (
    _context_source,
    _iid,
    _state_source,
    _swap_case,
)


def _extract(inputs: dict[str, object] | None = None):
    exact_inputs = _exact_inputs() if inputs is None else inputs
    return extract_source_bound_fee_occurrence_v1(
        state_source=exact_inputs["state_source"],
        settlement=exact_inputs["settlement"],
        intents=exact_inputs["intents"],
        context=exact_inputs["context"],
    )


def _nonzero_protocol_fee_inputs() -> tuple[dict[str, object], int, str]:
    state, intent, _settlement = _swap_case()
    share_bps = 5_000
    recipient = "0x" + "22" * 48
    settlement = compute_settlement(
        [intent],
        state.pools,
        state.balances,
        state.lp_balances,
        protocol_fee_share_bps=share_bps,
        protocol_fee_recipient_pubkey=recipient,
    )
    assert settlement.fills[0].protocol_fee_paid is not None
    assert settlement.fills[0].protocol_fee_paid > 0
    context = _context_source()
    context = replace(
        context,
        settlement=replace(
            context.settlement,
            protocol_fee_share_bps=share_bps,
            protocol_fee_recipient_pubkey=recipient,
        ),
    )
    return (
        {
            "state_source": _state_source(state),
            "settlement": snapshot_settlement(settlement),
            "intents": admit_intent_batch([intent]),
            "context": context,
        },
        settlement.fills[0].protocol_fee_paid,
        intent.fields["asset_in"],
    )


def test_extractor_has_no_candidate_or_caller_selected_root_arguments() -> None:
    assert tuple(signature(extract_source_bound_fee_occurrence_v1).parameters) == (
        "state_source",
        "settlement",
        "intents",
        "context",
    )


def test_zero_protocol_fee_remains_an_explicit_source_bound_witness() -> None:
    result = _extract()

    assert type(result) is SourceBoundFeeOccurrenceV1
    assert len(result.segment.ordered_witnesses) == 1
    witness = result.segment.ordered_witnesses[0]
    assert witness.position == 0
    assert witness.amount == 0
    assert witness.key.fee_distribution_domain_id == PROTOCOL_FEE_DISTRIBUTION_DOMAIN_ID_V1
    assert witness.key.asset == owned_intent_field_v1(
        result.material.intents[0],
        "asset_in",
    )
    assert len(witness.source_witness_root) == 64
    assert result.segment.boundary_root == result.boundary_root
    assert result.segment.policy_root == result.policy_root
    assert not hasattr(result, "evaluation")
    assert not hasattr(result, "post_state_root")
    assert verify_source_bound_fee_occurrence_v1(result) is None


def test_nonzero_protocol_fee_is_bound_to_the_direct_swap_input_asset() -> None:
    inputs, expected_fee, expected_asset = _nonzero_protocol_fee_inputs()
    result = _extract(inputs)

    assert type(result) is SourceBoundFeeOccurrenceV1
    assert result.segment.semantic_vector == (
        (result.segment.ordered_witnesses[0].key, expected_fee),
    )
    witness = result.segment.ordered_witnesses[0]
    assert witness.amount == expected_fee
    assert witness.key.asset == expected_asset


def test_two_direct_swap_witnesses_preserve_canonical_settlement_order() -> None:
    state, first, _settlement = _swap_case()
    second = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(2),
        sender_pubkey=first.sender_pubkey,
        deadline=first.deadline,
        fields={
            **first.fields,
            "amount_in": 75_000,
            "nonce": 2,
        },
    )
    share_bps = 5_000
    recipient = "0x" + "33" * 48
    settlement = compute_settlement(
        [first, second],
        state.pools,
        state.balances,
        state.lp_balances,
        protocol_fee_share_bps=share_bps,
        protocol_fee_recipient_pubkey=recipient,
    )
    context = _context_source()
    context = replace(
        context,
        settlement=replace(
            context.settlement,
            protocol_fee_share_bps=share_bps,
            protocol_fee_recipient_pubkey=recipient,
        ),
    )
    result = _extract(
        {
            "state_source": _state_source(state),
            "settlement": snapshot_settlement(settlement),
            "intents": admit_intent_batch([first, second]),
            "context": context,
        }
    )

    assert type(result) is SourceBoundFeeOccurrenceV1
    assert tuple(witness.position for witness in result.segment.ordered_witnesses) == (0, 1)
    assert len({witness.source_witness_root for witness in result.segment.ordered_witnesses}) == 2
    expected_order = tuple(
        fill.intent_id
        for fill in result.material.settlement.fills
        if fill.protocol_fee_paid is not None
    )
    assert (
        tuple(
            entry.intent_id
            for entry in result.settlement_index.entries
            if entry.fill is not None and entry.fill.protocol_fee_paid is not None
        )
        == expected_order
    )


def test_fee_policy_rotation_changes_occurrence_context_but_not_state_key() -> None:
    inputs = _exact_inputs()
    first = _extract(inputs)
    rotated_context = replace(
        inputs["context"],
        fee_split_policy=FCISFeeSplitPolicySourceV1(
            buyback_bps=10_000,
            treasury_bps=0,
            rewards_bps=0,
        ),
    )
    second = _extract({**inputs, "context": rotated_context})

    assert type(first) is SourceBoundFeeOccurrenceV1
    assert type(second) is SourceBoundFeeOccurrenceV1
    assert first.policy_root != second.policy_root
    assert first.segment.ordered_witnesses[0].key == second.segment.ordered_witnesses[0].key


def test_missing_distribution_policy_fails_closed_before_evaluation() -> None:
    inputs = _exact_inputs()
    context = replace(inputs["context"], fee_split_policy=None)
    result = _extract({**inputs, "context": context})

    assert type(result) is SourceBoundFeeOccurrenceRejectV1
    assert result.code is SourceBoundFeeOccurrenceCodeV1.MISSING_FEE_DISTRIBUTION_POLICY


def test_forged_exact_fill_rejects_before_witness_normalization() -> None:
    inputs = _exact_inputs()
    settlement = inputs["settlement"]
    forged_fill = replace(settlement.fills[0], protocol_fee_paid=1)
    forged_settlement = replace(settlement, fills=(forged_fill,))

    result = _extract({**inputs, "settlement": forged_settlement})

    assert type(result) is SourceBoundFeeOccurrenceRejectV1
    assert result.code is SourceBoundFeeOccurrenceCodeV1.SETTLEMENT_REPLAY_REJECTED


def test_corrupted_cached_source_root_fails_fresh_rederivation() -> None:
    result = _extract()
    assert type(result) is SourceBoundFeeOccurrenceV1
    object.__setattr__(result, "command_root", "0x" + "00" * 32)

    reject = verify_source_bound_fee_occurrence_v1(result)

    assert type(reject) is SourceBoundFeeOccurrenceRejectV1
    assert reject.code is SourceBoundFeeOccurrenceCodeV1.SOURCE_REDERIVATION_MISMATCH
