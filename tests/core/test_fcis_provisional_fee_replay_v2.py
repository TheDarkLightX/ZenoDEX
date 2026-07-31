"""V2 provisional-fee replay boundaries for the unmounted FCIS path."""

from __future__ import annotations

import pytest

from src.core.fcis_amm_dispatch import (
    CommittedPoolSwapQuoteV1,
    quote_exact_in_for_committed_pool_v1,
    quote_exact_out_for_committed_pool_v1,
)
from src.core.fcis_fee_occurrence_normal_form import (
    CanonicalFeeOccurrenceSegmentV1,
    canonicalize_fee_occurrence_segment_v1,
)
from src.core.fcis_pool_fingerprint import pool_state_fingerprint_committed_v1
from src.core.fcis_provisional_fee_replay_v2 import (
    replay_provisional_fee_swaps_v2,
)
from src.core.fcis_provisional_fee_replay_values_v2 import (
    ProvisionalFeeReplayCandidateV2,
    ProvisionalFeeReplayCodeV2,
    ProvisionalFeeReplayPolicyV2,
    ProvisionalFeeReplayRejectV2,
    ProvisionalQuotedSwapClaimV2,
    ProvisionalSwapKindV2,
    provisional_fee_witness_claims_v2,
)
from src.core.fcis_settlement_strong_validator import (
    evaluate_settlement_strong_exact_v1,
)
from src.core.fcis_settlement_strong_values import (
    ExactSpotPreStateV1,
    ExactStrongSettlementCandidateV1,
)
from src.core.settlement_snapshots import (
    OwnedBalanceDeltaV1,
    OwnedFillV1,
    OwnedReserveDeltaV1,
    OwnedSettlementV1,
    snapshot_settlement,
)
from src.state.state_snapshot_schema import StateEnumTagV1
from src.state.state_snapshot_values import CommittedPoolStateV1
from tests.core.test_fcis_settlement_strong_validator import (
    ASSET0,
    ASSET1,
    FEE_RECIPIENT,
    FILL_ACTION_FILL_ORDINAL,
    INITIAL_BALANCE,
    INTENT_KIND_SWAP_EXACT_IN_ORDINAL,
    INTENT_KIND_SWAP_EXACT_OUT_ORDINAL,
    OTHER_FEE_RECIPIENT,
    POOL_ID,
    SENDER,
    _balances,
    _context,
    _funded_pool,
    _intent,
    _lp_balances,
    _pools,
    _state_enum,
)

DOMAIN_ID = "protocol-fees"
PROTOCOL_FEE_SHARE_BPS = 5_000
FIRST_INTENT_ID = "0x" + f"{9901:064x}"
SECOND_INTENT_ID = "0x" + f"{9902:064x}"


def _pre_state() -> ExactSpotPreStateV1:
    return ExactSpotPreStateV1(
        balances=_balances(
            ((SENDER, ASSET0), INITIAL_BALANCE),
            ((SENDER, ASSET1), INITIAL_BALANCE),
        ),
        pools=_pools(_funded_pool()),
        lp_balances=_lp_balances(),
    )


def _policy() -> ProvisionalFeeReplayPolicyV2:
    return ProvisionalFeeReplayPolicyV2(
        fee_distribution_domain_id=DOMAIN_ID,
        protocol_fee_share_bps=PROTOCOL_FEE_SHARE_BPS,
    )


def _claim(
    *,
    position: int,
    kind: ProvisionalSwapKindV2,
    intent_id: str,
    sender: str,
    pool: CommittedPoolStateV1,
    amount_specified: int,
    limit_amount: int,
    quote: CommittedPoolSwapQuoteV1,
) -> ProvisionalQuotedSwapClaimV2:
    return ProvisionalQuotedSwapClaimV2(
        position=position,
        kind=kind,
        intent_id=intent_id,
        sender_pubkey=sender,
        recipient_pubkey=sender,
        pool_id=pool.pool_id,
        asset_in=ASSET0,
        asset_out=ASSET1,
        amount_specified=amount_specified,
        limit_amount=limit_amount,
        amount_in_filled=quote.amount_in,
        amount_out_filled=quote.amount_out,
        fee_paid=quote.fee_paid,
        protocol_fee_paid=quote.protocol_fee_paid,
    )


def _first_quote(pool: CommittedPoolStateV1) -> CommittedPoolSwapQuoteV1:
    return quote_exact_out_for_committed_pool_v1(
        pool,
        reserve_in=pool.reserve0,
        reserve_out=pool.reserve1,
        amount_out=10_000,
        protocol_fee_share_bps=PROTOCOL_FEE_SHARE_BPS,
    )


def _second_quote(
    pool_after_first: CommittedPoolStateV1,
) -> CommittedPoolSwapQuoteV1:
    return quote_exact_in_for_committed_pool_v1(
        pool_after_first,
        reserve_in=pool_after_first.reserve0,
        reserve_out=pool_after_first.reserve1,
        amount_in=10,
        protocol_fee_share_bps=PROTOCOL_FEE_SHARE_BPS,
    )


def _two_swap_claims() -> tuple[
    tuple[ProvisionalQuotedSwapClaimV2, ProvisionalQuotedSwapClaimV2],
    CommittedPoolSwapQuoteV1,
    CommittedPoolSwapQuoteV1,
]:
    pool = _funded_pool()
    first_quote = _first_quote(pool)
    pool_after_first = CommittedPoolStateV1(
        pool_id=pool.pool_id,
        asset0=pool.asset0,
        asset1=pool.asset1,
        reserve0=first_quote.new_reserve_in,
        reserve1=first_quote.new_reserve_out,
        fee_bps=pool.fee_bps,
        lp_supply=pool.lp_supply,
        status=pool.status,
        created_at=pool.created_at,
        curve_tag=pool.curve_tag,
        curve_params=pool.curve_params,
    )
    second_quote = _second_quote(pool_after_first)
    return (
        (
            _claim(
                position=0,
                kind=ProvisionalSwapKindV2.EXACT_OUT,
                intent_id=FIRST_INTENT_ID,
                sender=SENDER,
                pool=pool,
                amount_specified=10_000,
                limit_amount=1_000_000,
                quote=first_quote,
            ),
            _claim(
                position=1,
                kind=ProvisionalSwapKindV2.EXACT_IN,
                intent_id=SECOND_INTENT_ID,
                sender=FEE_RECIPIENT,
                pool=pool_after_first,
                amount_specified=10,
                limit_amount=0,
                quote=second_quote,
            ),
        ),
        first_quote,
        second_quote,
    )


def _legacy_v1_graph(
    first_quote: CommittedPoolSwapQuoteV1,
    second_quote: CommittedPoolSwapQuoteV1,
):
    first_intent = _intent(
        member_ordinal=INTENT_KIND_SWAP_EXACT_OUT_ORDINAL,
        kind_name="swap_exact_out",
        intent_id=FIRST_INTENT_ID,
        fields=(
            ("pool_id", POOL_ID),
            ("asset_in", ASSET0),
            ("asset_out", ASSET1),
            ("amount_out", 10_000),
            ("max_amount_in", 1_000_000),
        ),
    )
    second_intent = _intent(
        member_ordinal=INTENT_KIND_SWAP_EXACT_IN_ORDINAL,
        kind_name="swap_exact_in",
        intent_id=SECOND_INTENT_ID,
        sender_pubkey=FEE_RECIPIENT,
        fields=(
            ("pool_id", POOL_ID),
            ("asset_in", ASSET0),
            ("asset_out", ASSET1),
            ("amount_in", 10),
            ("min_amount_out", 0),
        ),
    )
    action = _state_enum(StateEnumTagV1.FILL_ACTION, FILL_ACTION_FILL_ORDINAL)
    settlement = snapshot_settlement(
        OwnedSettlementV1(
            module="TauSwap",
            version="0.1",
            batch_ref="v1-spendable-protocol-fee",
            included_intents=(
                (FIRST_INTENT_ID, action),
                (SECOND_INTENT_ID, action),
            ),
            fills=(
                OwnedFillV1(
                    FIRST_INTENT_ID,
                    action,
                    None,
                    first_quote.amount_in,
                    first_quote.amount_out,
                    first_quote.fee_paid,
                    first_quote.protocol_fee_paid,
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                ),
                OwnedFillV1(
                    SECOND_INTENT_ID,
                    action,
                    None,
                    second_quote.amount_in,
                    second_quote.amount_out,
                    second_quote.fee_paid,
                    second_quote.protocol_fee_paid,
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                ),
            ),
            balance_deltas=(
                OwnedBalanceDeltaV1(SENDER, ASSET0, 0, first_quote.amount_in),
                OwnedBalanceDeltaV1(SENDER, ASSET1, first_quote.amount_out, 0),
                OwnedBalanceDeltaV1(
                    FEE_RECIPIENT,
                    ASSET0,
                    first_quote.protocol_fee_paid,
                    second_quote.amount_in,
                ),
                OwnedBalanceDeltaV1(
                    FEE_RECIPIENT,
                    ASSET1,
                    second_quote.amount_out,
                    0,
                ),
            ),
            reserve_deltas=(
                OwnedReserveDeltaV1(
                    POOL_ID,
                    ASSET0,
                    first_quote.amount_in
                    - first_quote.protocol_fee_paid
                    + second_quote.amount_in
                    - second_quote.protocol_fee_paid,
                    0,
                ),
                OwnedReserveDeltaV1(
                    POOL_ID,
                    ASSET1,
                    0,
                    first_quote.amount_out + second_quote.amount_out,
                ),
            ),
            lp_deltas=(),
            events=None,
        )
    )
    return settlement, (first_intent, second_intent)


def test_v1_accepts_fee_credit_that_v2_keeps_provisional() -> None:
    _claims, first_quote, second_quote = _two_swap_claims()
    settlement, intents = _legacy_v1_graph(first_quote, second_quote)

    observed = evaluate_settlement_strong_exact_v1(
        settlement,
        intents,
        _pre_state(),
        _context(
            protocol_fee_share_bps=PROTOCOL_FEE_SHARE_BPS,
            protocol_fee_recipient_pubkey=FEE_RECIPIENT,
        ),
    )

    assert type(observed.result) is ExactStrongSettlementCandidateV1
    assert first_quote.protocol_fee_paid > second_quote.amount_in


def test_v2_rejects_later_same_batch_spend_of_provisional_fee() -> None:
    claims, _first_quote, _second_quote = _two_swap_claims()

    result = replay_provisional_fee_swaps_v2(
        claims,
        _pre_state(),
        _policy(),
    )

    assert type(result) is ProvisionalFeeReplayRejectV2
    assert result.code is ProvisionalFeeReplayCodeV2.STATE_TRANSITION_REJECTED
    assert result.position == 1
    assert not hasattr(result, "post_state")
    assert not hasattr(result, "fee_witnesses")


def test_v2_single_swap_retains_fee_as_exact_slnf_source_witness() -> None:
    pool = _funded_pool()
    quote = quote_exact_in_for_committed_pool_v1(
        pool,
        reserve_in=pool.reserve0,
        reserve_out=pool.reserve1,
        amount_in=1_000,
        protocol_fee_share_bps=PROTOCOL_FEE_SHARE_BPS,
    )
    claim = _claim(
        position=0,
        kind=ProvisionalSwapKindV2.EXACT_IN,
        intent_id=FIRST_INTENT_ID,
        sender=SENDER,
        pool=pool,
        amount_specified=1_000,
        limit_amount=0,
        quote=quote,
    )

    result = replay_provisional_fee_swaps_v2(
        (claim,),
        _pre_state(),
        _policy(),
    )

    assert type(result) is ProvisionalFeeReplayCandidateV2
    assert result.post_state.balances.get(SENDER, ASSET0) == INITIAL_BALANCE - quote.amount_in
    assert result.post_state.balances.get(FEE_RECIPIENT, ASSET0) == 0
    assert result.post_state.pools[POOL_ID].reserve0 == quote.new_reserve_in
    assert len(result.fee_witnesses) == 1
    witness = result.fee_witnesses[0]
    assert witness.pool_snapshot_fingerprint == pool_state_fingerprint_committed_v1(pool)
    assert witness.sender_input_debit == quote.amount_in
    assert witness.pool_reserve_credit == quote.amount_in - quote.protocol_fee_paid
    assert witness.provisional_fee_amount == quote.protocol_fee_paid
    assert witness.sender_input_debit == (
        witness.pool_reserve_credit + witness.provisional_fee_amount
    )

    claims = provisional_fee_witness_claims_v2(result)
    assert len(claims) == 1
    assert claims[0].position == 0
    assert claims[0].key.fee_distribution_domain_id == DOMAIN_ID
    assert claims[0].key.asset == ASSET0
    assert claims[0].amount == quote.protocol_fee_paid
    assert claims[0].source_witness_root == witness.source_witness_root

    segment = canonicalize_fee_occurrence_segment_v1(
        boundary_root="11" * 32,
        policy_root="22" * 32,
        witnesses=claims,
    )
    assert type(segment) is CanonicalFeeOccurrenceSegmentV1
    assert segment.ordered_witnesses == claims
    assert segment.semantic_vector == ((claims[0].key, quote.protocol_fee_paid),)


def test_v2_equal_inputs_replay_deterministically() -> None:
    pool = _funded_pool()
    quote = _first_quote(pool)
    claim = _claim(
        position=0,
        kind=ProvisionalSwapKindV2.EXACT_OUT,
        intent_id=FIRST_INTENT_ID,
        sender=SENDER,
        pool=pool,
        amount_specified=10_000,
        limit_amount=1_000_000,
        quote=quote,
    )

    first = replay_provisional_fee_swaps_v2((claim,), _pre_state(), _policy())
    second = replay_provisional_fee_swaps_v2((claim,), _pre_state(), _policy())

    assert first == second


def test_v2_rejects_noncanonical_fill_positions_before_replay() -> None:
    pool = _funded_pool()
    quote = _first_quote(pool)
    claim = _claim(
        position=1,
        kind=ProvisionalSwapKindV2.EXACT_OUT,
        intent_id=FIRST_INTENT_ID,
        sender=SENDER,
        pool=pool,
        amount_specified=10_000,
        limit_amount=1_000_000,
        quote=quote,
    )

    result = replay_provisional_fee_swaps_v2((claim,), _pre_state(), _policy())

    assert type(result) is ProvisionalFeeReplayRejectV2
    assert result.code is ProvisionalFeeReplayCodeV2.NONCANONICAL_POSITION
    assert result.position == 0
    assert not hasattr(result, "post_state")


def test_v2_rejects_declared_fill_that_differs_from_fresh_quote() -> None:
    pool = _funded_pool()
    quote = _first_quote(pool)
    claim = _claim(
        position=0,
        kind=ProvisionalSwapKindV2.EXACT_OUT,
        intent_id=FIRST_INTENT_ID,
        sender=SENDER,
        pool=pool,
        amount_specified=10_000,
        limit_amount=1_000_000,
        quote=quote,
    )
    object.__setattr__(claim, "amount_out_filled", quote.amount_out + 1)

    result = replay_provisional_fee_swaps_v2((claim,), _pre_state(), _policy())

    assert type(result) is ProvisionalFeeReplayRejectV2
    assert result.code is ProvisionalFeeReplayCodeV2.DECLARED_FILL_MISMATCH
    assert result.position == 0
    assert not hasattr(result, "post_state")


def test_v2_rejects_duplicate_intent_identity_before_replay() -> None:
    claims, _first_quote, _second_quote = _two_swap_claims()
    object.__setattr__(claims[1], "intent_id", claims[0].intent_id)

    result = replay_provisional_fee_swaps_v2(claims, _pre_state(), _policy())

    assert type(result) is ProvisionalFeeReplayRejectV2
    assert result.code is ProvisionalFeeReplayCodeV2.DUPLICATE_INTENT
    assert result.position is None
    assert not hasattr(result, "post_state")


def test_v2_projection_rejects_post_replay_lineage_mutation() -> None:
    pool = _funded_pool()
    quote = _first_quote(pool)
    claim = _claim(
        position=0,
        kind=ProvisionalSwapKindV2.EXACT_OUT,
        intent_id=FIRST_INTENT_ID,
        sender=SENDER,
        pool=pool,
        amount_specified=10_000,
        limit_amount=1_000_000,
        quote=quote,
    )
    result = replay_provisional_fee_swaps_v2((claim,), _pre_state(), _policy())
    assert type(result) is ProvisionalFeeReplayCandidateV2
    object.__setattr__(result.fee_witnesses[0], "recipient_pubkey", OTHER_FEE_RECIPIENT)

    with pytest.raises(ValueError, match="witness root mismatch"):
        provisional_fee_witness_claims_v2(result)


def test_v2_projection_rejects_pool_snapshot_fingerprint_mutation() -> None:
    pool = _funded_pool()
    quote = _first_quote(pool)
    claim = _claim(
        position=0,
        kind=ProvisionalSwapKindV2.EXACT_OUT,
        intent_id=FIRST_INTENT_ID,
        sender=SENDER,
        pool=pool,
        amount_specified=10_000,
        limit_amount=1_000_000,
        quote=quote,
    )
    result = replay_provisional_fee_swaps_v2((claim,), _pre_state(), _policy())
    assert type(result) is ProvisionalFeeReplayCandidateV2
    object.__setattr__(result.fee_witnesses[0], "pool_snapshot_fingerprint", "0x" + "00" * 32)

    with pytest.raises(ValueError, match="witness root mismatch"):
        provisional_fee_witness_claims_v2(result)


def test_v2_revalidates_mutated_claim_before_state_reads() -> None:
    pool = _funded_pool()
    quote = _first_quote(pool)
    claim = _claim(
        position=0,
        kind=ProvisionalSwapKindV2.EXACT_OUT,
        intent_id=FIRST_INTENT_ID,
        sender=SENDER,
        pool=pool,
        amount_specified=10_000,
        limit_amount=1_000_000,
        quote=quote,
    )
    object.__setattr__(claim, "amount_in_filled", True)

    result = replay_provisional_fee_swaps_v2(
        (claim,),
        _pre_state(),
        _policy(),
    )

    assert type(result) is ProvisionalFeeReplayRejectV2
    assert result.code is ProvisionalFeeReplayCodeV2.INVALID_INPUT
    assert result.position == 0
