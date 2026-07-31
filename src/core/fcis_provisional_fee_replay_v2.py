"""Pure unmounted V2 quoted-swap replay with provisional protocol fees."""

from __future__ import annotations

from dataclasses import dataclass
from typing import cast, final

from ..state.fcis_curve_config import CURVE_TAG_CPMM
from ..state.fcis_spot_replay import (
    FCISSpotReplayDeltaBatchV1,
    FCISSpotReplayOkV1,
    apply_fcis_spot_replay_observed_v1,
)
from ..state.state_snapshot_values import (
    POOL_STATUS_ACTIVE_MEMBER_ORDINAL_V1,
    CommittedPoolStateV1,
)
from ..state.state_transitions import BalanceDeltaV1, PoolReserveDeltaV1
from .fcis_amm_dispatch import (
    CommittedPoolSwapQuoteV1,
    quote_exact_in_for_committed_pool_v1,
    quote_exact_out_for_committed_pool_v1,
)
from .fcis_fee_apportionment_values import MAX_FEE_AMOUNT_CANDIDATES_V2
from .fcis_pool_fingerprint import pool_state_fingerprint_committed_v1
from .fcis_provisional_fee_replay_values_v2 import (
    _PROVISIONAL_FEE_REPLAY_TOKEN_V2,
    ProvisionalFeeReplayCandidateV2,
    ProvisionalFeeReplayCodeV2,
    ProvisionalFeeReplayPolicyV2,
    ProvisionalFeeReplayRejectV2,
    ProvisionalFeeReplayResultV2,
    ProvisionalProtocolFeeWitnessV2,
    ProvisionalQuotedSwapClaimV2,
    ProvisionalSwapKindV2,
    _admit_context_v2,
    _reject_v2,
    _source_witness_root_v2,
)
from .fcis_settlement_strong_values import ExactSpotPreStateV1


@final
@dataclass(frozen=True, slots=True)
class _ReplayStepOkV2:
    state: ExactSpotPreStateV1
    witness: ProvisionalProtocolFeeWitnessV2 | None


@final
@dataclass(frozen=True, slots=True)
class _OrientedPoolV2:
    pool: CommittedPoolStateV1
    reserve_in: int
    reserve_out: int
    zero_for_one: bool


@final
@dataclass(frozen=True, slots=True)
class _QuotedReplayPlanV2:
    oriented_pool: _OrientedPoolV2
    quote: CommittedPoolSwapQuoteV1


def _orientation_v2(
    pool: CommittedPoolStateV1,
    asset_in: str,
    asset_out: str,
) -> _OrientedPoolV2 | None:
    if (asset_in, asset_out) == (pool.asset0, pool.asset1):
        return _OrientedPoolV2(
            pool=pool,
            reserve_in=pool.reserve0,
            reserve_out=pool.reserve1,
            zero_for_one=True,
        )
    if (asset_in, asset_out) == (pool.asset1, pool.asset0):
        return _OrientedPoolV2(
            pool=pool,
            reserve_in=pool.reserve1,
            reserve_out=pool.reserve0,
            zero_for_one=False,
        )
    return None


def _quote_v2(
    claim: ProvisionalQuotedSwapClaimV2,
    oriented_pool: _OrientedPoolV2,
    policy: ProvisionalFeeReplayPolicyV2,
) -> CommittedPoolSwapQuoteV1:
    pool = oriented_pool.pool
    if claim.kind is ProvisionalSwapKindV2.EXACT_IN:
        return quote_exact_in_for_committed_pool_v1(
            pool,
            reserve_in=oriented_pool.reserve_in,
            reserve_out=oriented_pool.reserve_out,
            amount_in=claim.amount_specified,
            protocol_fee_share_bps=policy.protocol_fee_share_bps,
        )
    return quote_exact_out_for_committed_pool_v1(
        pool,
        reserve_in=oriented_pool.reserve_in,
        reserve_out=oriented_pool.reserve_out,
        amount_out=claim.amount_specified,
        protocol_fee_share_bps=policy.protocol_fee_share_bps,
    )


def _quote_matches_claim_v2(
    claim: ProvisionalQuotedSwapClaimV2,
    quote: CommittedPoolSwapQuoteV1,
) -> bool:
    return (
        claim.amount_in_filled,
        claim.amount_out_filled,
        claim.fee_paid,
        claim.protocol_fee_paid,
    ) == (
        quote.amount_in,
        quote.amount_out,
        quote.fee_paid,
        quote.protocol_fee_paid,
    )


def _slippage_holds_v2(
    claim: ProvisionalQuotedSwapClaimV2,
    quote: CommittedPoolSwapQuoteV1,
) -> bool:
    if claim.kind is ProvisionalSwapKindV2.EXACT_IN:
        return quote.amount_out >= claim.limit_amount
    return quote.amount_in <= claim.limit_amount


def _build_witness_v2(
    claim: ProvisionalQuotedSwapClaimV2,
    policy: ProvisionalFeeReplayPolicyV2,
    plan: _QuotedReplayPlanV2,
) -> ProvisionalProtocolFeeWitnessV2 | None:
    quote = plan.quote
    oriented_pool = plan.oriented_pool
    if quote.protocol_fee_paid == 0:
        return None
    fields: dict[str, str | int] = {
        "fill_position": claim.position,
        "intent_id": claim.intent_id,
        "pool_snapshot_fingerprint": pool_state_fingerprint_committed_v1(oriented_pool.pool),
        "fee_distribution_domain_id": policy.fee_distribution_domain_id,
        "pool_id": claim.pool_id,
        "asset": claim.asset_in,
        "sender_pubkey": claim.sender_pubkey,
        "swap_kind": claim.kind.value,
        "recipient_pubkey": claim.recipient_pubkey,
        "asset_out": claim.asset_out,
        "amount_specified": claim.amount_specified,
        "limit_amount": claim.limit_amount,
        "recipient_output_credit": quote.amount_out,
        "total_fee_amount": quote.fee_paid,
        "protocol_fee_share_bps": policy.protocol_fee_share_bps,
        "sender_input_debit": quote.amount_in,
        "pool_reserve_credit": quote.amount_in - quote.protocol_fee_paid,
        "provisional_fee_amount": quote.protocol_fee_paid,
        "reserve_in_before": oriented_pool.reserve_in,
        "reserve_out_before": oriented_pool.reserve_out,
        "reserve_in_after": quote.new_reserve_in,
        "reserve_out_after": quote.new_reserve_out,
    }
    return ProvisionalProtocolFeeWitnessV2(
        fill_position=claim.position,
        intent_id=claim.intent_id,
        fee_distribution_domain_id=policy.fee_distribution_domain_id,
        pool_snapshot_fingerprint=pool_state_fingerprint_committed_v1(oriented_pool.pool),
        pool_id=claim.pool_id,
        asset=claim.asset_in,
        sender_pubkey=claim.sender_pubkey,
        kind=claim.kind,
        recipient_pubkey=claim.recipient_pubkey,
        asset_out=claim.asset_out,
        amount_specified=claim.amount_specified,
        limit_amount=claim.limit_amount,
        recipient_output_credit=quote.amount_out,
        total_fee_amount=quote.fee_paid,
        protocol_fee_share_bps=policy.protocol_fee_share_bps,
        sender_input_debit=quote.amount_in,
        pool_reserve_credit=quote.amount_in - quote.protocol_fee_paid,
        provisional_fee_amount=quote.protocol_fee_paid,
        reserve_in_before=oriented_pool.reserve_in,
        reserve_out_before=oriented_pool.reserve_out,
        reserve_in_after=quote.new_reserve_in,
        reserve_out_after=quote.new_reserve_out,
        source_witness_root=_source_witness_root_v2(fields),
        _construction_token=_PROVISIONAL_FEE_REPLAY_TOKEN_V2,
    )


def _prepare_quote_plan_v2(
    claim: ProvisionalQuotedSwapClaimV2,
    state: ExactSpotPreStateV1,
    policy: ProvisionalFeeReplayPolicyV2,
) -> _QuotedReplayPlanV2 | ProvisionalFeeReplayRejectV2:
    pool = state.pools.get(claim.pool_id)
    if pool is None:
        return _reject_v2(
            ProvisionalFeeReplayCodeV2.POOL_NOT_FOUND,
            claim.position,
            f"pool not found: {claim.pool_id}",
        )
    if pool.status.member_ordinal != POOL_STATUS_ACTIVE_MEMBER_ORDINAL_V1:
        return _reject_v2(
            ProvisionalFeeReplayCodeV2.POOL_NOT_ACTIVE,
            claim.position,
            f"pool is not active: {claim.pool_id}",
        )
    oriented_pool = _orientation_v2(pool, claim.asset_in, claim.asset_out)
    if oriented_pool is None:
        return _reject_v2(
            ProvisionalFeeReplayCodeV2.ASSET_MISMATCH,
            claim.position,
            f"swap assets do not match pool: {claim.pool_id}",
        )
    if policy.protocol_fee_share_bps and pool.curve_tag != CURVE_TAG_CPMM:
        return _reject_v2(
            ProvisionalFeeReplayCodeV2.UNSUPPORTED_PROTOCOL_FEE_CURVE,
            claim.position,
            f"protocol fees require CPMM: {claim.pool_id}",
        )
    try:
        quote = _quote_v2(claim, oriented_pool, policy)
    except (ArithmeticError, TypeError, ValueError) as exc:
        return _reject_v2(
            ProvisionalFeeReplayCodeV2.QUOTE_REJECTED,
            claim.position,
            str(exc),
        )
    if not _quote_matches_claim_v2(claim, quote):
        return _reject_v2(
            ProvisionalFeeReplayCodeV2.DECLARED_FILL_MISMATCH,
            claim.position,
            "declared fill disagrees with recomputed quote",
        )
    if not _slippage_holds_v2(claim, quote):
        return _reject_v2(
            ProvisionalFeeReplayCodeV2.SLIPPAGE,
            claim.position,
            "recomputed quote violates the declared limit",
        )
    return _QuotedReplayPlanV2(oriented_pool=oriented_pool, quote=quote)


def _delta_batch_v2(
    claim: ProvisionalQuotedSwapClaimV2,
    quote: CommittedPoolSwapQuoteV1,
) -> FCISSpotReplayDeltaBatchV1:
    return FCISSpotReplayDeltaBatchV1(
        balance_deltas=(
            BalanceDeltaV1(
                (claim.sender_pubkey, claim.asset_in),
                -quote.amount_in,
            ),
            BalanceDeltaV1(
                (claim.recipient_pubkey, claim.asset_out),
                quote.amount_out,
            ),
        ),
        reserve_deltas=(
            PoolReserveDeltaV1(
                claim.pool_id,
                claim.asset_in,
                quote.amount_in - quote.protocol_fee_paid,
            ),
            PoolReserveDeltaV1(
                claim.pool_id,
                claim.asset_out,
                -quote.amount_out,
            ),
        ),
        lp_deltas=(),
        pool_creations=(),
    )


def _replay_one_v2(
    claim: ProvisionalQuotedSwapClaimV2,
    state: ExactSpotPreStateV1,
    policy: ProvisionalFeeReplayPolicyV2,
) -> _ReplayStepOkV2 | ProvisionalFeeReplayRejectV2:
    plan = _prepare_quote_plan_v2(claim, state, policy)
    if type(plan) is ProvisionalFeeReplayRejectV2:
        return plan
    quote = plan.quote
    deltas = _delta_batch_v2(claim, quote)
    replayed, _reads = apply_fcis_spot_replay_observed_v1(
        state.balances,
        state.pools,
        state.lp_balances,
        deltas,
    )
    if type(replayed) is not FCISSpotReplayOkV1:
        code = getattr(replayed, "code", type(replayed).__name__)
        return _reject_v2(
            ProvisionalFeeReplayCodeV2.STATE_TRANSITION_REJECTED,
            claim.position,
            f"spot replay rejected: {getattr(code, 'value', code)}",
        )
    next_state = ExactSpotPreStateV1(
        balances=replayed.balances,
        pools=replayed.pools,
        lp_balances=replayed.lp_balances,
    )
    post_pool = next_state.pools.get(claim.pool_id)
    expected_reserves = (
        (quote.new_reserve_in, quote.new_reserve_out)
        if plan.oriented_pool.zero_for_one
        else (quote.new_reserve_out, quote.new_reserve_in)
    )
    if post_pool is None or (post_pool.reserve0, post_pool.reserve1) != expected_reserves:
        return _reject_v2(
            ProvisionalFeeReplayCodeV2.POST_STATE_MISMATCH,
            claim.position,
            "spot replay disagrees with recomputed quote reserves",
        )
    return _ReplayStepOkV2(
        state=next_state,
        witness=_build_witness_v2(
            claim,
            policy,
            plan,
        ),
    )


def _admit_claims_v2(
    claims: object,
) -> tuple[ProvisionalQuotedSwapClaimV2, ...] | ProvisionalFeeReplayRejectV2:
    if type(claims) is not tuple:
        return _reject_v2(
            ProvisionalFeeReplayCodeV2.INVALID_INPUT,
            None,
            "claims must be an exact tuple",
        )
    exact_claim_objects = cast(tuple[object, ...], claims)
    if len(exact_claim_objects) > MAX_FEE_AMOUNT_CANDIDATES_V2:
        return _reject_v2(
            ProvisionalFeeReplayCodeV2.INVALID_INPUT,
            None,
            "claim count exceeds the bounded replay limit",
        )
    typed_claims: list[ProvisionalQuotedSwapClaimV2] = []
    for position, claim_object in enumerate(exact_claim_objects):
        if type(claim_object) is not ProvisionalQuotedSwapClaimV2:
            return _reject_v2(
                ProvisionalFeeReplayCodeV2.INVALID_INPUT,
                position,
                "claim must be exact",
            )
        claim = claim_object
        try:
            claim.__post_init__()
        except (ArithmeticError, TypeError, ValueError) as exc:
            return _reject_v2(
                ProvisionalFeeReplayCodeV2.INVALID_INPUT,
                position,
                str(exc),
            )
        if claim.position != position:
            return _reject_v2(
                ProvisionalFeeReplayCodeV2.NONCANONICAL_POSITION,
                position,
                "claim positions must equal canonical tuple positions",
            )
        typed_claims.append(claim)
    intent_ids = tuple(claim.intent_id for claim in typed_claims)
    if len(intent_ids) != len(set(intent_ids)):
        return _reject_v2(
            ProvisionalFeeReplayCodeV2.DUPLICATE_INTENT,
            None,
            "claim tuple contains duplicate intent identifiers",
        )
    return tuple(typed_claims)


def _fold_replay_v2(
    claims: tuple[ProvisionalQuotedSwapClaimV2, ...],
    pre_state: ExactSpotPreStateV1,
    policy: ProvisionalFeeReplayPolicyV2,
) -> ProvisionalFeeReplayResultV2:
    state = pre_state
    witnesses: list[ProvisionalProtocolFeeWitnessV2] = []
    for claim in claims:
        step = _replay_one_v2(claim, state, policy)
        if type(step) is ProvisionalFeeReplayRejectV2:
            return step
        state = step.state
        if step.witness is not None:
            witnesses.append(step.witness)
    return ProvisionalFeeReplayCandidateV2(
        post_state=state,
        fee_witnesses=tuple(witnesses),
        _construction_token=_PROVISIONAL_FEE_REPLAY_TOKEN_V2,
    )


def replay_provisional_fee_swaps_v2(
    claims: object,
    pre_state: object,
    policy: object,
) -> ProvisionalFeeReplayResultV2:
    """Recompute an ordered quoted-swap fold with non-spendable protocol fees."""

    admitted_claims = _admit_claims_v2(claims)
    if type(admitted_claims) is ProvisionalFeeReplayRejectV2:
        return admitted_claims
    admitted_context = _admit_context_v2(pre_state, policy)
    if type(admitted_context) is ProvisionalFeeReplayRejectV2:
        return admitted_context
    exact_pre_state, exact_policy = admitted_context
    return _fold_replay_v2(
        admitted_claims,
        exact_pre_state,
        exact_policy,
    )


__all__ = ("replay_provisional_fee_swaps_v2",)
