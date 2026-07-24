"""
Strong settlement validation (proof-carrying friendly).

The legacy validator in `src/core/batch_clearing.py` checks conservation and
non-negativity of the *net* deltas, but it does not bind those deltas to:
  - the user intents (min_out / max_in constraints, recipient rules, etc.)
  - the verified swap kernels (no "k decreases" / free value leaks)

This module treats the settlement as an *untrusted certificate* and replay-
verifies the batch by re-executing each filled intent against local copies of
state using the verified kernels (`amm_dispatch`, `lp_math_v7`, etc). It then
recomputes canonical deltas/events and requires exact match.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple, TypeAlias, final

from ..kernels.python.settlement_swap_runtime_v1 import quote_cpmm_swap_exact_out
from ..state.balances import AssetId, BalanceTable, PubKey
from ..state.intents import Intent, IntentKind
from ..state.legacy_state_snapshots import (
    admit_legacy_balance_for_differential_v1,
    admit_legacy_lp_for_differential_v1,
    admit_legacy_pool_map_for_differential_v1,
)
from ..state.lp import LPTable
from ..state.lp_duration_transitions import (
    LPDurationEventV1,
    LPDurationRiskPolicyV1,
)
from ..state.owned_collections import OwnedMapV1
from ..state.pool_creation_transition import PoolCreationV1
from ..state.pools import (
    CURVE_TAG_CPMM,
    PoolState,
    compute_pool_id,
    normalize_curve_config,
)
from ..state.spot_state_transitions import (
    SpotDeltaBatchV1,
    SpotTransitionOkV1,
    SpotTransitionRejectV1,
    _apply_spot_replay_deltas_v1,
    _SpotReplayDeltaBatchV1,
    _SpotReplayOkV1,
    _SpotReplayTransitionRejectV1,
    apply_spot_deltas_v1,
)
from ..state.state_snapshot_values import (
    POOL_STATUS_ACTIVE_MEMBER_ORDINAL_V1,
    POOL_STATUS_MEMBER_VALUES_V1,
    CommittedBalanceTableV1,
    CommittedLPTableV1,
    CommittedPoolStateV1,
)
from ..state.state_snapshots import (
    snapshot_balance_table,
    snapshot_lp_table,
    snapshot_pool_map,
)
from ..state.state_transitions import (
    BalanceDeltaV1,
    CanonicalBalancePatchV1,
    CanonicalLPPositionPatchV1,
    CanonicalPoolPatchV1,
    LPPositionDeltaV1,
    PoolReserveDeltaV1,
)
from .amm_dispatch import (
    swap_exact_in_for_committed_pool_v1,
    swap_exact_out_for_committed_pool_v1,
)
from .cpmm import (
    MIN_LP_LOCK,
    compute_fee_total,
    compute_lp_mint,
    swap_exact_in_with_protocol_fee,
)
from .domain_limits import DEX_LP_AMOUNT_MAX, is_strict_int, require_int_range
from .liquidity import (
    AddLiquidityKernelInputV1,
    RemoveLiquidityKernelInputV1,
    add_liquidity_for_committed_pool_v1,
    remove_liquidity_for_committed_pool_v1,
)
from .quote_receipts import pool_state_fingerprint_committed_v1
from .route_settlement import (
    ROUTE_REJECT_POOL_STATE_DRIFT,
    ROUTE_RESERVED_FIELDS,
    is_route_intent_kind,
    parse_route_binding_fields,
    replay_route_legs_committed_v1,
    route_binding_pins_committed_snapshot_v1,
    route_totals_violation,
    validate_route_intent_against_binding,
)
from .settlement import BalanceDelta, Fill, FillAction, LPDelta, ReserveDelta, Settlement

LP_LOCK_PUBKEY: PubKey = "0x" + "00" * 48

_MODE_STRONG_REPLAY = "strong_replay"
_MODE_STRONG_PROOF_CARRYING = "strong_proof_carrying"
_VALIDATION_MODES = frozenset({_MODE_STRONG_REPLAY, _MODE_STRONG_PROOF_CARRYING})


@final
@dataclass(frozen=True, slots=True)
class _ExactSpotReplayStateV1:
    balances: CommittedBalanceTableV1
    pools: OwnedMapV1[str, CommittedPoolStateV1]
    lp_balances: CommittedLPTableV1

    def __post_init__(self) -> None:
        if type(self.balances) is not CommittedBalanceTableV1:
            raise TypeError("replay balances must be exact committed state")
        if type(self.pools) is not OwnedMapV1:
            raise TypeError("replay pools must be an exact committed map")
        if type(self.lp_balances) is not CommittedLPTableV1:
            raise TypeError("replay LP balances must be exact committed state")


@final
@dataclass(frozen=True, slots=True)
class _SpotTransitionContextV1:
    """Explicit context retained until the duration-complete candidate is built."""

    now: int
    min_lp_position_age_seconds: int
    lp_duration_policy: LPDurationRiskPolicyV1 | None


@final
@dataclass(frozen=True, slots=True)
class _ValidationOnlyOutputV1:
    """Request replay validation without constructing an authority candidate."""


@final
@dataclass(frozen=True, slots=True)
class _DurationCandidateOutputV1:
    """Request the one duration-complete candidate after replay validation."""

    context: _SpotTransitionContextV1


@final
@dataclass(frozen=True, slots=True)
class StrongSettlementStateCandidateV1:
    """Complete exact spot successor produced by one validated settlement replay.

    This is the PR #477 state candidate. The supplied settlement and aggregate
    effects remain legacy values until PR #478 owns that authority graph, so
    this value alone does not authorize shell commitment.
    """

    balances: CommittedBalanceTableV1
    pools: OwnedMapV1[str, CommittedPoolStateV1]
    lp_balances: CommittedLPTableV1
    balance_patch: CanonicalBalancePatchV1 | None
    pool_patch: CanonicalPoolPatchV1 | None
    lp_patch: CanonicalLPPositionPatchV1 | None

    def __post_init__(self) -> None:
        _ExactSpotReplayStateV1(
            self.balances,
            self.pools,
            self.lp_balances,
        )
        if (
            self.balance_patch is not None
            and type(self.balance_patch) is not CanonicalBalancePatchV1
        ):
            raise TypeError("strong settlement balance patch must be exact or None")
        if self.pool_patch is not None and type(self.pool_patch) is not CanonicalPoolPatchV1:
            raise TypeError("strong settlement pool patch must be exact or None")
        if self.lp_patch is not None and type(self.lp_patch) is not CanonicalLPPositionPatchV1:
            raise TypeError("strong settlement LP patch must be exact or None")


@final
@dataclass(frozen=True, slots=True)
class StrongSettlementRejectV1:
    """Typed no-candidate rejection preserving the mounted public reason."""

    reason: str

    def __post_init__(self) -> None:
        if type(self.reason) is not str or not self.reason:
            raise TypeError("strong settlement rejection requires an exact reason")


StrongSettlementEvaluationResultV1: TypeAlias = (
    StrongSettlementStateCandidateV1 | StrongSettlementRejectV1
)


@final
@dataclass(frozen=True, slots=True)
class _StrongSettlementReplayAcceptedV1:
    """Private validation-only success; carries no committable candidate."""


_StrongSettlementInternalResultV1: TypeAlias = (
    StrongSettlementEvaluationResultV1 | _StrongSettlementReplayAcceptedV1
)


_LegacyOrExactBalanceV1: TypeAlias = BalanceTable | CommittedBalanceTableV1
_LegacyOrExactPoolMapV1: TypeAlias = Dict[str, PoolState] | OwnedMapV1[str, CommittedPoolStateV1]
_LegacyOrExactLPV1: TypeAlias = LPTable | CommittedLPTableV1


def _admit_exact_replay_state_v1(
    pre_balances: _LegacyOrExactBalanceV1,
    pre_pools: _LegacyOrExactPoolMapV1,
    pre_lp_balances: _LegacyOrExactLPV1 | None,
) -> _ExactSpotReplayStateV1:
    balances = (
        snapshot_balance_table(pre_balances)
        if type(pre_balances) is CommittedBalanceTableV1
        else admit_legacy_balance_for_differential_v1(pre_balances)
    )
    pools = (
        snapshot_pool_map(pre_pools)
        if type(pre_pools) is OwnedMapV1
        else admit_legacy_pool_map_for_differential_v1(pre_pools)
    )
    lp_source = pre_lp_balances if pre_lp_balances is not None else LPTable()
    lp_balances = (
        snapshot_lp_table(lp_source)
        if type(lp_source) is CommittedLPTableV1
        else admit_legacy_lp_for_differential_v1(lp_source)
    )
    return _ExactSpotReplayStateV1(
        balances=balances,
        pools=pools,
        lp_balances=lp_balances,
    )


@final
@dataclass(frozen=True, slots=True)
class _SpotReplayRejectV1:
    code: str
    path: tuple[str | int, ...]

    def text(self) -> str:
        path = ".".join(str(part) for part in self.path)
        return self.code if not path else f"{self.code}:{path}"


_SpotReplayResultV1: TypeAlias = _ExactSpotReplayStateV1 | _SpotReplayRejectV1


def _spot_reject_v1(
    reject: SpotTransitionRejectV1 | _SpotReplayTransitionRejectV1,
) -> _SpotReplayRejectV1:
    return _SpotReplayRejectV1(reject.code.value, reject.path)


def _apply_spot_replay_v1(
    state: _ExactSpotReplayStateV1,
    deltas: _SpotReplayDeltaBatchV1,
) -> _SpotReplayResultV1:
    result = _apply_spot_replay_deltas_v1(
        state.balances,
        state.pools,
        state.lp_balances,
        deltas,
    )
    if type(result) is not _SpotReplayOkV1:
        return _spot_reject_v1(result)
    return _ExactSpotReplayStateV1(
        result.balances,
        result.pools,
        result.lp_balances,
    )


def _strong_reject_v1(reason: str | None) -> StrongSettlementRejectV1:
    return StrongSettlementRejectV1(
        reason if type(reason) is str and reason else "settlement invalid"
    )


def _strong_result_tuple_v1(
    result: _StrongSettlementInternalResultV1,
) -> Tuple[bool, Optional[str]]:
    if type(result) is StrongSettlementRejectV1:
        return False, result.reason
    return True, None


def _build_exact_spot_batch_v1(
    balance_deltas: List[BalanceDelta],
    reserve_deltas: List[ReserveDelta],
    lp_deltas: List[LPDelta],
    pool_creations: List[PoolCreationV1],
) -> SpotDeltaBatchV1 | StrongSettlementRejectV1:
    """Lower trusted replay output into the public duration-aware command."""

    try:
        return SpotDeltaBatchV1(
            balance_deltas=tuple(
                BalanceDeltaV1(
                    (delta.pubkey, delta.asset),
                    delta.delta_add - delta.delta_sub,
                )
                for delta in balance_deltas
                if delta.delta_add != delta.delta_sub
            ),
            reserve_deltas=tuple(
                PoolReserveDeltaV1(
                    delta.pool_id,
                    delta.asset,
                    delta.delta_add - delta.delta_sub,
                )
                for delta in reserve_deltas
                if delta.delta_add != delta.delta_sub
            ),
            lp_events=tuple(
                LPDurationEventV1(
                    (delta.pubkey, delta.pool_id),
                    delta.delta_add,
                    delta.delta_sub,
                )
                for delta in lp_deltas
            ),
            pool_creations=tuple(pool_creations),
        )
    except (TypeError, ValueError) as exc:
        return _strong_reject_v1(
            f"exact spot command construction failed after replay: {type(exc).__name__}: {exc}"
        )


def _build_exact_spot_candidate_v1(
    pre_state: _ExactSpotReplayStateV1,
    replay_state: _ExactSpotReplayStateV1,
    exact_batch: SpotDeltaBatchV1,
    context: _SpotTransitionContextV1,
) -> StrongSettlementEvaluationResultV1:
    """Build one authoritative candidate and require exact replay agreement."""

    exact_candidate = apply_spot_deltas_v1(
        pre_state.balances,
        pre_state.pools,
        pre_state.lp_balances,
        exact_batch,
        now=context.now,
        min_age_seconds=context.min_lp_position_age_seconds,
        policy=context.lp_duration_policy,
    )
    if type(exact_candidate) is not SpotTransitionOkV1:
        rejected = _spot_reject_v1(exact_candidate)
        return _strong_reject_v1(f"exact spot candidate rejected: {rejected.text()}")
    if exact_candidate.balances != replay_state.balances:
        return _strong_reject_v1("exact spot candidate balance mismatch vs sequential replay")
    if exact_candidate.pools != replay_state.pools:
        return _strong_reject_v1("exact spot candidate pool mismatch vs sequential replay")
    if exact_candidate.lp_balances.balance_entries != replay_state.lp_balances.balance_entries:
        return _strong_reject_v1("exact spot candidate LP-balance mismatch vs sequential replay")
    return StrongSettlementStateCandidateV1(
        balances=exact_candidate.balances,
        pools=exact_candidate.pools,
        lp_balances=exact_candidate.lp_balances,
        balance_patch=exact_candidate.balance_patch,
        pool_patch=exact_candidate.pool_patch,
        lp_patch=exact_candidate.lp_patch,
    )


def _pool_status_text_v1(pool: CommittedPoolStateV1) -> str:
    return f"PoolStatus.{POOL_STATUS_MEMBER_VALUES_V1[pool.status.member_ordinal]}"


def _pool_reserves_match_quote_v1(
    pool: CommittedPoolStateV1,
    dir_is_0_to_1: bool,
    new_in: int,
    new_out: int,
) -> bool:
    expected = (new_in, new_out) if dir_is_0_to_1 else (new_out, new_in)
    return (pool.reserve0, pool.reserve1) == expected


@final
@dataclass(frozen=True, slots=True)
class _PoolSwapApplyV1:
    pool_id: str
    sender: PubKey
    recipient: PubKey
    asset_in: AssetId
    asset_out: AssetId
    amount_in: int
    amount_out: int
    protocol_fee: int
    protocol_fee_recipient: PubKey | None


def _apply_pool_swap_spot_v1(
    state: _ExactSpotReplayStateV1,
    change: _PoolSwapApplyV1,
) -> _SpotReplayResultV1:
    protocol_fee_recipient = change.protocol_fee_recipient
    balance_deltas = [
        BalanceDeltaV1((change.sender, change.asset_in), -change.amount_in),
        BalanceDeltaV1((change.recipient, change.asset_out), change.amount_out),
    ]
    if change.protocol_fee:
        if protocol_fee_recipient is None:
            return _SpotReplayRejectV1(
                "protocol_fee present without recipient",
                (),
            )
        balance_deltas.append(
            BalanceDeltaV1(
                (protocol_fee_recipient, change.asset_in),
                change.protocol_fee,
            )
        )
    pool_input = change.amount_in - change.protocol_fee
    reserve_deltas = [
        PoolReserveDeltaV1(
            change.pool_id,
            change.asset_out,
            -change.amount_out,
        )
    ]
    if pool_input:
        reserve_deltas.append(
            PoolReserveDeltaV1(
                change.pool_id,
                change.asset_in,
                pool_input,
            )
        )
    return _apply_spot_replay_v1(
        state,
        _SpotReplayDeltaBatchV1(
            balance_deltas=tuple(balance_deltas),
            reserve_deltas=tuple(reserve_deltas),
            lp_deltas=(),
            pool_creations=(),
        ),
    )


def _format_error_details(**kwargs: object) -> str:
    parts: list[str] = []
    for key, value in kwargs.items():
        if value is None:
            continue
        parts.append(f"{key}={value!r}")
    return ", ".join(parts)


def _quote_binding_error(reason: str, **kwargs: object) -> str:
    details = _format_error_details(**kwargs)
    if not details:
        return reason
    return f"{reason}: {details}"


def _quote_binding_context(intent: Intent) -> dict[str, object]:
    return {
        "intent_id": intent.intent_id,
        "quote_hash": intent.get_field("quote_receipt_hash"),
        "quote_pool_fingerprint": intent.get_field("quote_pool_fingerprint"),
        "leg_index": intent.get_field("quote_receipt_leg_index"),
        "pool_id": intent.get_field("pool_id"),
    }


@dataclass(frozen=True)
class _CowPairEntry:
    intent_id: str
    pool_id: str
    asset_in: AssetId
    asset_out: AssetId
    amount_in_filled: int
    amount_out_filled: int


@dataclass(frozen=True)
class _SettlementIndex:
    intents_by_id: Dict[str, Intent]
    fill_by_id: Dict[str, Fill]


def _validate_cow_pair_index(
    *,
    settlement: Settlement,
    intents_by_id: Dict[str, Intent],
    fill_by_id: Dict[str, Fill],
    allow_cow_netting: bool,
) -> Tuple[bool, Optional[str]]:
    cow_ids = [fill.intent_id for fill in settlement.fills if fill.reason == "COW_NETTED"]
    if not cow_ids:
        return True, None
    if not allow_cow_netting:
        return False, f"COW_NETTED not allowed for intent_id={cow_ids[0]}"

    entries: Dict[str, _CowPairEntry] = {}
    for intent_id in cow_ids:
        it = intents_by_id[intent_id]
        f = fill_by_id[intent_id]
        if f.action != FillAction.FILL:
            return False, f"COW_NETTED requires filled action: intent_id={intent_id}"
        if it.kind != IntentKind.SWAP_EXACT_IN:
            return False, f"COW_NETTED only supported for SWAP_EXACT_IN: intent_id={intent_id}"

        pool_id = it.get_field("pool_id")
        if not isinstance(pool_id, str) or not pool_id:
            return False, f"missing pool_id for intent_id={intent_id}"
        asset_in = it.get_field("asset_in")
        asset_out = it.get_field("asset_out")
        if not isinstance(asset_in, str) or not isinstance(asset_out, str):
            return False, f"invalid asset_in/out for intent_id={intent_id}"
        amount_in = it.get_field("amount_in")
        min_out = it.get_field("min_amount_out", 0)
        if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
            return False, f"invalid amount_in for intent_id={intent_id}"
        if not isinstance(min_out, int) or isinstance(min_out, bool) or min_out < 0:
            return False, f"invalid min_amount_out for intent_id={intent_id}"
        if int(f.fee_paid or 0) != 0:
            return False, f"COW_NETTED fee_paid must be 0: intent_id={intent_id}"
        if not is_strict_int(f.amount_in_filled) or int(f.amount_in_filled or 0) != int(amount_in):
            return False, f"COW_NETTED amount_in_filled mismatch: intent_id={intent_id}"
        if not is_strict_int(f.amount_out_filled):
            return False, f"COW_NETTED amount_out_filled invalid: intent_id={intent_id}"
        out_amt = int(f.amount_out_filled or 0)
        if out_amt < int(min_out):
            return False, f"COW_NETTED slippage: intent_id={intent_id}"
        entries[intent_id] = _CowPairEntry(
            intent_id=intent_id,
            pool_id=pool_id,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in_filled=int(f.amount_in_filled or 0),
            amount_out_filled=out_amt,
        )

    pair_for: Dict[str, str] = {}
    for intent_id, entry in entries.items():
        matches = [
            other_id
            for other_id, other in entries.items()
            if other_id != intent_id
            and other.pool_id == entry.pool_id
            and other.asset_in == entry.asset_out
            and other.asset_out == entry.asset_in
            and other.amount_in_filled == entry.amount_out_filled
            and other.amount_out_filled == entry.amount_in_filled
        ]
        if len(matches) != 1:
            return (
                False,
                f"COW_NETTED fill requires exactly one reciprocal counterparty: intent_id={intent_id} matches={matches}",
            )
        pair_for[intent_id] = matches[0]

    for intent_id, counterparty_id in pair_for.items():
        if pair_for.get(counterparty_id) != intent_id:
            return False, f"COW_NETTED reciprocal pair is not symmetric: intent_id={intent_id}"
    return True, None


def _build_settlement_index(
    *,
    settlement: Settlement,
    intents: List[Intent],
    allow_cow_netting: bool,
) -> Tuple[bool, Optional[str], Optional[_SettlementIndex]]:
    """Validate intent/fill membership and build replay lookup tables.

    This is the validator's front-door shape check. It does no state replay; it
    only proves that every later lookup by `intent_id` is total and unambiguous.
    """
    intent_ids = [it.intent_id for it in intents]
    if len(intent_ids) != len(set(intent_ids)):
        return False, "duplicate intent_id in input intents", None

    intents_by_id: Dict[str, Intent] = {it.intent_id: it for it in intents}

    included_ids = [intent_id for intent_id, _action in settlement.included_intents]
    if set(included_ids) != set(intent_ids):
        missing = sorted(set(intent_ids) - set(included_ids))
        extra = sorted(set(included_ids) - set(intent_ids))
        return False, f"settlement included_intents mismatch: missing={missing} extra={extra}", None
    if len(included_ids) != len(set(included_ids)):
        return False, "settlement included_intents contains duplicate intent_id entries", None

    fill_ids = [f.intent_id for f in settlement.fills]
    if len(fill_ids) != len(set(fill_ids)):
        return False, "settlement fills contains duplicate intent_id entries", None
    extra_fill_ids = sorted(set(fill_ids) - set(intent_ids))
    if extra_fill_ids:
        return (
            False,
            f"settlement fills contains intent_ids not in input intents: {extra_fill_ids}",
            None,
        )

    fill_by_id: Dict[str, Fill] = {f.intent_id: f for f in settlement.fills}
    for intent_id, action in settlement.included_intents:
        f = fill_by_id.get(intent_id)
        if f is None:
            if action == FillAction.FILL:
                return False, f"missing Fill for filled intent_id: {intent_id}", None
            continue
        if f.action != action:
            return (
                False,
                f"Fill.action mismatch for intent_id={intent_id}: {f.action} != {action}",
                None,
            )

    ok_cow, err_cow = _validate_cow_pair_index(
        settlement=settlement,
        intents_by_id=intents_by_id,
        fill_by_id=fill_by_id,
        allow_cow_netting=allow_cow_netting,
    )
    if not ok_cow:
        return False, err_cow, None

    return True, None, _SettlementIndex(intents_by_id=intents_by_id, fill_by_id=fill_by_id)


def _validate_quote_binding_metadata(
    intent: Intent,
    *,
    allow_snapshot_bound_quote_bindings: bool,
) -> Optional[str]:
    """Validate transport-level quote metadata before replaying an intent.

    The strong validator only accepts sanitized pool-snapshot fingerprints here.
    Receipt hashes and leg indexes must be discharged by the engine witness path.
    """
    quote_receipt_hash = intent.get_field("quote_receipt_hash")
    quote_pool_fp = intent.get_field("quote_pool_fingerprint")
    quote_leg_index = intent.get_field("quote_receipt_leg_index")
    has_quote_binding = (
        quote_receipt_hash is not None or quote_pool_fp is not None or quote_leg_index is not None
    )
    if has_quote_binding and intent.kind not in (
        IntentKind.SWAP_EXACT_IN,
        IntentKind.SWAP_EXACT_OUT,
    ):
        return _quote_binding_error(
            "quote receipt binding only supported for swap intents",
            **_quote_binding_context(intent),
            intent_kind=intent.kind.value,
        )
    if quote_leg_index is not None and (
        not is_strict_int(quote_leg_index) or int(quote_leg_index) < 0
    ):
        return _quote_binding_error(
            "invalid quote_receipt_leg_index", **_quote_binding_context(intent)
        )
    if quote_leg_index is not None:
        return _quote_binding_error(
            "quote receipt transport metadata requires validated engine witness",
            **_quote_binding_context(intent),
            guidance="strip quote_receipt_hash and quote_receipt_leg_index after engine witness validation",
        )
    if quote_receipt_hash is not None:
        if not isinstance(quote_receipt_hash, str) or not quote_receipt_hash:
            return _quote_binding_error(
                "invalid quote_receipt_hash", **_quote_binding_context(intent)
            )
        return _quote_binding_error(
            "quote receipt transport metadata requires validated engine witness",
            **_quote_binding_context(intent),
            guidance="strip quote_receipt_hash and quote_receipt_leg_index after engine witness validation",
        )
    if quote_pool_fp is not None and (not isinstance(quote_pool_fp, str) or not quote_pool_fp):
        return _quote_binding_error(
            "missing quote_pool_fingerprint", **_quote_binding_context(intent)
        )
    if quote_pool_fp is not None and not allow_snapshot_bound_quote_bindings:
        return _quote_binding_error(
            "quote receipt snapshot binding requires validated engine witness",
            **_quote_binding_context(intent),
            guidance="only pass sanitized quote_pool_fingerprint through the validated engine path",
        )
    return None


def validate_settlement_strong(
    *,
    settlement: Settlement,
    intents: List[Intent],
    pre_balances: BalanceTable,
    pre_pools: Dict[str, PoolState],
    pre_lp_balances: Optional[LPTable] = None,
    mode: str = _MODE_STRONG_REPLAY,
    allow_cow_netting: bool = False,
    allow_snapshot_bound_quote_bindings: bool = False,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: Optional[PubKey] = None,
) -> Tuple[bool, Optional[str]]:
    """
    Fail-closed wrapper around the strong validator implementation.

    This validator is used on untrusted settlement proposals; it must return `(False, reason)`
    rather than crash on malformed inputs.
    """
    try:
        replay_state = _admit_exact_replay_state_v1(
            pre_balances,
            pre_pools,
            pre_lp_balances,
        )
        return _strong_result_tuple_v1(
            _validate_settlement_strong_impl(
                settlement=settlement,
                intents=intents,
                pre_balances=replay_state.balances,
                pre_pools=replay_state.pools,
                pre_lp_balances=replay_state.lp_balances,
                mode=mode,
                allow_cow_netting=allow_cow_netting,
                allow_snapshot_bound_quote_bindings=allow_snapshot_bound_quote_bindings,
                protocol_fee_share_bps=protocol_fee_share_bps,
                protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
                output_plan=_ValidationOnlyOutputV1(),
            )
        )
    except Exception as exc:
        return _strong_crash_result_v1(exc)


def validate_settlement_strong_committed_v1(
    *,
    settlement: Settlement,
    intents: List[Intent],
    pre_balances: CommittedBalanceTableV1,
    pre_pools: OwnedMapV1[str, CommittedPoolStateV1],
    pre_lp_balances: CommittedLPTableV1,
    now: int,
    min_lp_position_age_seconds: int,
    lp_duration_policy: LPDurationRiskPolicyV1 | None,
    mode: str = _MODE_STRONG_REPLAY,
    allow_cow_netting: bool = False,
    allow_snapshot_bound_quote_bindings: bool = False,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: Optional[PubKey] = None,
) -> Tuple[bool, Optional[str]]:
    """Validate against exact committed values through the same replay relation."""

    return _strong_result_tuple_v1(
        evaluate_settlement_strong_committed_v1(
            settlement=settlement,
            intents=intents,
            pre_balances=pre_balances,
            pre_pools=pre_pools,
            pre_lp_balances=pre_lp_balances,
            now=now,
            min_lp_position_age_seconds=min_lp_position_age_seconds,
            lp_duration_policy=lp_duration_policy,
            mode=mode,
            allow_cow_netting=allow_cow_netting,
            allow_snapshot_bound_quote_bindings=allow_snapshot_bound_quote_bindings,
            protocol_fee_share_bps=protocol_fee_share_bps,
            protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
        )
    )


def evaluate_settlement_strong_committed_v1(
    *,
    settlement: Settlement,
    intents: List[Intent],
    pre_balances: CommittedBalanceTableV1,
    pre_pools: OwnedMapV1[str, CommittedPoolStateV1],
    pre_lp_balances: CommittedLPTableV1,
    now: int,
    min_lp_position_age_seconds: int,
    lp_duration_policy: LPDurationRiskPolicyV1 | None,
    mode: str = _MODE_STRONG_REPLAY,
    allow_cow_netting: bool = False,
    allow_snapshot_bound_quote_bindings: bool = False,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: Optional[PubKey] = None,
) -> StrongSettlementEvaluationResultV1:
    """Evaluate once and retain the exact successor used by strong replay."""

    try:
        replay_state = _ExactSpotReplayStateV1(
            pre_balances,
            pre_pools,
            pre_lp_balances,
        )
        result = _validate_settlement_strong_impl(
            settlement=settlement,
            intents=intents,
            pre_balances=replay_state.balances,
            pre_pools=replay_state.pools,
            pre_lp_balances=replay_state.lp_balances,
            mode=mode,
            allow_cow_netting=allow_cow_netting,
            allow_snapshot_bound_quote_bindings=allow_snapshot_bound_quote_bindings,
            protocol_fee_share_bps=protocol_fee_share_bps,
            protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
            output_plan=_DurationCandidateOutputV1(
                _SpotTransitionContextV1(
                    now,
                    min_lp_position_age_seconds,
                    lp_duration_policy,
                )
            ),
        )
        if type(result) is _StrongSettlementReplayAcceptedV1:
            return _strong_reject_v1(
                "strong validator returned validation-only success for exact evaluation"
            )
        return result
    except Exception as exc:
        return _strong_reject_v1(_strong_crash_text_v1(exc))


def _strong_crash_result_v1(exc: Exception) -> Tuple[bool, str]:
    return False, _strong_crash_text_v1(exc)


def _strong_crash_text_v1(exc: Exception) -> str:
    detail = str(exc).strip()
    if "\n" in detail or "\r" in detail:
        detail = " ".join(detail.split())
    if len(detail) > 200:
        detail = detail[:200]
    if detail:
        return f"strong validator crashed: {type(exc).__name__}: {detail}"
    return f"strong validator crashed: {type(exc).__name__}"


def _validate_settlement_strong_impl(
    *,
    settlement: Settlement,
    intents: List[Intent],
    pre_balances: CommittedBalanceTableV1,
    pre_pools: OwnedMapV1[str, CommittedPoolStateV1],
    pre_lp_balances: CommittedLPTableV1,
    output_plan: object,
    mode: str = _MODE_STRONG_REPLAY,
    allow_cow_netting: bool = False,
    allow_snapshot_bound_quote_bindings: bool = False,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: Optional[PubKey] = None,
) -> _StrongSettlementInternalResultV1:
    """
    Strong settlement validation.

    This is intended to be used in `dex.step` as a fail-closed acceptance gate.
    """
    if mode not in _VALIDATION_MODES:
        return _strong_reject_v1(f"unsupported validation mode: {mode!r}")
    if (
        type(output_plan) is not _ValidationOnlyOutputV1
        and type(output_plan) is not _DurationCandidateOutputV1
    ):
        return _strong_reject_v1("unsupported strong settlement output plan")
    if not is_strict_int(protocol_fee_share_bps) or not (0 <= protocol_fee_share_bps <= 10000):
        return _strong_reject_v1("protocol_fee_share_bps must be an int in [0, 10000]")
    if protocol_fee_share_bps > 0 and not protocol_fee_recipient_pubkey:
        return _strong_reject_v1(
            "protocol_fee_recipient_pubkey is required when protocol_fee_share_bps > 0"
        )

    ok_index, err_index, settlement_index = _build_settlement_index(
        settlement=settlement,
        allow_cow_netting=allow_cow_netting,
        intents=intents,
    )
    if not ok_index or settlement_index is None:
        return _strong_reject_v1(err_index)
    intents_by_id = settlement_index.intents_by_id
    fill_by_id = settlement_index.fill_by_id

    # Canonical route discipline. compute_settlement clears intents in strict
    # phase order: CREATE_POOL (phase 0) -> routes in ascending intent_id
    # (phase 1) -> per-pool batches and non-pool rejects (phase 2). Routes are
    # snapshot-bound, so their FILL/REJECT outcome depends on replay position;
    # without pinning the phase order a forged settlement could pick the
    # non-canonical winner between two routes sharing a pool, interleave a
    # fill before a route to fake a "justified" drift reject, or move a
    # CREATE_POOL after a route so it spends balance the route just produced
    # (canonical compute creates pools first, before that balance exists).
    # Enforce this ONLY when routes are present (leaves non-route settlements,
    # whose phase order the legacy replay does not pin, byte-for-byte
    # unchanged).
    route_entry_ids = [
        intent_id
        for intent_id, _action in settlement.included_intents
        if is_route_intent_kind(intents_by_id[intent_id].kind)
    ]
    if route_entry_ids:
        if route_entry_ids != sorted(route_entry_ids):
            return _strong_reject_v1("route intents must be settled in ascending intent_id order")

        def _settlement_phase(intent_id: str) -> int:
            kind = intents_by_id[intent_id].kind
            if kind == IntentKind.CREATE_POOL:
                return 0
            if is_route_intent_kind(kind):
                return 1
            return 2

        prev_phase = 0
        for intent_id, _action in settlement.included_intents:
            phase = _settlement_phase(intent_id)
            if phase < prev_phase:
                return _strong_reject_v1(
                    "non-canonical settlement phase order at intent_id="
                    f"{intent_id}: routes require CREATE_POOL before route "
                    "before other pool intents"
                )
            prev_phase = phase

    # Replay state is one immutable exact aggregate. Each accepted intent
    # replaces this local value with a complete candidate; rejection retains
    # the prior aggregate and exposes no partial successor.
    pre_replay_state = _ExactSpotReplayStateV1(
        pre_balances,
        pre_pools,
        pre_lp_balances,
    )
    replay_state = pre_replay_state

    expected_events: List[dict] = []
    bal_deltas: List[BalanceDelta] = []
    res_deltas: List[ReserveDelta] = []
    lp_deltas: List[LPDelta] = []
    exact_pool_creations: List[PoolCreationV1] = []

    def fail(msg: str) -> StrongSettlementRejectV1:
        return _strong_reject_v1(msg)

    for intent_id, action in settlement.included_intents:
        it = intents_by_id[intent_id]
        quote_binding_error = _validate_quote_binding_metadata(
            it,
            allow_snapshot_bound_quote_bindings=allow_snapshot_bound_quote_bindings,
        )
        if quote_binding_error is not None:
            return fail(quote_binding_error)
        quote_pool_fp = it.get_field("quote_pool_fingerprint")
        has_route_binding_fields = any(
            it.get_field(field) is not None for field in ROUTE_RESERVED_FIELDS
        )
        if has_route_binding_fields and not is_route_intent_kind(it.kind):
            return fail(
                f"route binding fields only supported for route intents: "
                f"intent_id={it.intent_id} intent_kind={it.kind.value}"
            )
        if (
            is_route_intent_kind(it.kind)
            and has_route_binding_fields
            and not allow_snapshot_bound_quote_bindings
        ):
            return fail(
                f"route binding requires validated engine witness: intent_id={it.intent_id}"
            )

        if action == FillAction.REJECT:
            if is_route_intent_kind(it.kind) and allow_snapshot_bound_quote_bindings:
                # Must-fill discipline for the engine path. The engine injects
                # an authentic binding (legs + pool fingerprints) for EVERY
                # admitted route, filled or rejected, so under the engine
                # gate a route REJECT must carry a well-formed, intent-
                # consistent binding. A stripped binding (no fields) or a
                # tampered binding (parse fails / does not match the signed
                # route) cannot have come from the validated engine path, and
                # silently accepting such a REJECT would let a competing route
                # win the shared pool. Fail closed on all three; only a clean
                # binding whose replay genuinely cannot fill (drift, totals,
                # or insufficient balance at this position) justifies the
                # REJECT.
                if not has_route_binding_fields:
                    return fail(f"route reject missing engine binding: intent_id={intent_id}")
                binding, parse_err = parse_route_binding_fields(it)
                if binding is None:
                    return fail(
                        f"route binding invalid for rejected intent_id={intent_id}: {parse_err}"
                    )
                bind_err = validate_route_intent_against_binding(it, binding)
                if bind_err is not None:
                    return fail(
                        f"route reject binding mismatch for intent_id={intent_id}: {bind_err}"
                    )
                # Authenticity anchor: an authentic binding pins the pre-state
                # snapshot. A binding whose fingerprints match neither pre- nor
                # current-state would forge a fake ROUTE_POOL_STATE_DRIFT and
                # "justify" the reject; reject it before classifying drift.
                if not route_binding_pins_committed_snapshot_v1(binding, pre_pools):
                    return fail(
                        "route reject binding does not pin the pre-state snapshot "
                        f"for intent_id={intent_id}"
                    )
                replay = replay_route_legs_committed_v1(
                    binding=binding,
                    pools=replay_state.pools,
                )
                if replay.ok:
                    # Legs replayed exactly and totals are satisfiable (the
                    # binding matches the signed route), so the only canonical
                    # reason this route would not fill is the sender cannot
                    # afford the route total. Anything else means a FILL was
                    # due and the REJECT is a lie.
                    if route_totals_violation(it, replay) is not None:
                        return fail(f"route reject totals inconsistent for intent_id={intent_id}")
                    reject_sender: PubKey = it.sender_pubkey
                    if replay_state.balances.get(
                        reject_sender,
                        binding.asset_in,
                    ) >= int(replay.total_amount_in):
                        return fail(
                            "route reject not justified — canonical clearing "
                            f"would fill intent_id={intent_id}"
                        )
                elif replay.reject_reason != ROUTE_REJECT_POOL_STATE_DRIFT:
                    # Replay failed for a reason OTHER than genuine snapshot
                    # drift (fingerprints still match the current pools but the
                    # kernel disagrees with the claimed leg amounts, or the
                    # binding references a missing/invalid pool). An authentic
                    # engine-injected binding can only fail replay via drift;
                    # any other failure means the supplied binding is
                    # inconsistent with the snapshot it pins — tampered. Fail
                    # closed rather than letting it "justify" the REJECT.
                    return fail(
                        "route reject binding inconsistent with pinned snapshot "
                        f"for intent_id={intent_id}: {replay.reject_reason}"
                    )
                # else: genuine ROUTE_POOL_STATE_DRIFT — a canonical reject.
            continue

        f = fill_by_id[intent_id]

        sender: PubKey = it.sender_pubkey
        recipient: PubKey = it.get_field("recipient", sender)
        if not isinstance(recipient, str) or not recipient:
            return fail(f"invalid recipient for intent_id={intent_id}")

        if it.kind == IntentKind.CREATE_POOL:
            asset0 = it.get_field("asset0")
            asset1 = it.get_field("asset1")
            fee_bps = it.get_field("fee_bps")
            amount0 = it.get_field("amount0")
            amount1 = it.get_field("amount1")
            created_at = it.get_field("created_at", 0)
            curve_tag = it.get_field("curve_tag", None)
            curve_params = it.get_field("curve_params", None)
            if any(v is None for v in (asset0, asset1, fee_bps, amount0, amount1)):
                return fail(f"missing CREATE_POOL fields for intent_id={intent_id}")
            if not isinstance(asset0, str) or not isinstance(asset1, str):
                return fail(f"invalid CREATE_POOL asset ids for intent_id={intent_id}")
            if not is_strict_int(fee_bps) or not (0 <= fee_bps <= 10000):
                return fail(f"invalid CREATE_POOL fee_bps for intent_id={intent_id}")
            if not is_strict_int(amount0) or amount0 <= 0:
                return fail(f"invalid CREATE_POOL amount0 for intent_id={intent_id}")
            if not is_strict_int(amount1) or amount1 <= 0:
                return fail(f"invalid CREATE_POOL amount1 for intent_id={intent_id}")
            if created_at is not None and (not is_strict_int(created_at) or created_at < 0):
                return fail(f"invalid CREATE_POOL created_at for intent_id={intent_id}")
            created_at_value = 0 if created_at is None else created_at

            try:
                if asset0 >= asset1:
                    raise ValueError(f"Assets must be in canonical order: {asset0} < {asset1}")
                require_int_range(
                    "amount0",
                    amount0,
                    minimum=1,
                    maximum=DEX_LP_AMOUNT_MAX,
                )
                require_int_range(
                    "amount1",
                    amount1,
                    minimum=1,
                    maximum=DEX_LP_AMOUNT_MAX,
                )
                require_int_range("fee_bps", fee_bps, minimum=0, maximum=10_000)
                require_int_range("created_at", created_at_value, minimum=0)
                curve_tag_norm, curve_params_norm = normalize_curve_config(
                    curve_tag=curve_tag,
                    curve_params=curve_params,
                )
                pool_id = compute_pool_id(
                    asset0,
                    asset1,
                    fee_bps,
                    curve_tag=curve_tag_norm,
                    curve_params=curve_params_norm,
                )
                lp_minted = compute_lp_mint(
                    amount0,
                    amount1,
                    amount0,
                    amount1,
                    0,
                )
                pool_creation = PoolCreationV1(
                    pool_id=pool_id,
                    asset0=asset0,
                    asset1=asset1,
                    fee_bps=fee_bps,
                    created_at=created_at_value,
                    curve_tag=curve_tag_norm,
                    curve_params=curve_params_norm,
                )
            except (ArithmeticError, TypeError, ValueError) as exc:
                return fail(f"CREATE_POOL computation error for intent_id={intent_id}: {exc}")

            if pool_id in replay_state.pools:
                return fail(f"CREATE_POOL duplicates existing pool_id={pool_id}")

            # Fill must match the create_pool kernel.
            if int(f.amount0_used or 0) != int(amount0):
                return fail(f"CREATE_POOL fill.amount0_used mismatch for intent_id={intent_id}")
            if int(f.amount1_used or 0) != int(amount1):
                return fail(f"CREATE_POOL fill.amount1_used mismatch for intent_id={intent_id}")
            if int(f.lp_minted or 0) != int(lp_minted):
                return fail(f"CREATE_POOL fill.lp_minted mismatch for intent_id={intent_id}")

            try:
                applied = _apply_spot_replay_v1(
                    replay_state,
                    _SpotReplayDeltaBatchV1(
                        balance_deltas=(
                            BalanceDeltaV1((sender, asset0), -amount0),
                            BalanceDeltaV1((sender, asset1), -amount1),
                        ),
                        reserve_deltas=(
                            PoolReserveDeltaV1(pool_id, asset0, amount0),
                            PoolReserveDeltaV1(pool_id, asset1, amount1),
                        ),
                        lp_deltas=(
                            LPPositionDeltaV1((sender, pool_id), lp_minted),
                            LPPositionDeltaV1(
                                (LP_LOCK_PUBKEY, pool_id),
                                MIN_LP_LOCK,
                            ),
                        ),
                        pool_creations=(pool_creation,),
                    ),
                )
                if isinstance(applied, _SpotReplayRejectV1):
                    raise ValueError(applied.text())
                replay_state = applied
            except (TypeError, ValueError) as exc:
                return fail(f"CREATE_POOL balance/LP apply error for intent_id={intent_id}: {exc}")
            created_pool = replay_state.pools[pool_id]
            exact_pool_creations.append(pool_creation)

            # Expected events and deltas (canonicalized later).
            expected_events.append(
                {
                    "type": "CREATE_POOL",
                    "pool_id": pool_id,
                    "asset0": asset0,
                    "asset1": asset1,
                    "fee_bps": int(fee_bps),
                    "curve_tag": created_pool.curve_tag,
                    "curve_params": created_pool.curve_params,
                    "status": POOL_STATUS_MEMBER_VALUES_V1[POOL_STATUS_ACTIVE_MEMBER_ORDINAL_V1],
                    "created_at": int(created_pool.created_at),
                }
            )

            bal_deltas.append(
                BalanceDelta(pubkey=sender, asset=asset0, delta_add=0, delta_sub=int(amount0))
            )
            bal_deltas.append(
                BalanceDelta(pubkey=sender, asset=asset1, delta_add=0, delta_sub=int(amount1))
            )

            res_deltas.append(
                ReserveDelta(pool_id=pool_id, asset=asset0, delta_add=int(amount0), delta_sub=0)
            )
            res_deltas.append(
                ReserveDelta(pool_id=pool_id, asset=asset1, delta_add=int(amount1), delta_sub=0)
            )

            lp_deltas.append(
                LPDelta(pubkey=sender, pool_id=pool_id, delta_add=int(lp_minted), delta_sub=0)
            )
            lp_deltas.append(
                LPDelta(
                    pubkey=LP_LOCK_PUBKEY, pool_id=pool_id, delta_add=int(MIN_LP_LOCK), delta_sub=0
                )
            )
            continue

        if is_route_intent_kind(it.kind):
            # Atomic route fill: re-parse the engine-injected binding
            # (untrusted), re-validate it against the signed route fields, and
            # replay every leg with the verified kernels against the CURRENT
            # local replay state. Exact-quote semantics: any drift fails the
            # settlement (a computed settlement only ever FILLs a route that
            # replays exactly at this same position in included_intents order).
            binding, parse_err = parse_route_binding_fields(it)
            if binding is None:
                return fail(f"route binding invalid for intent_id={intent_id}: {parse_err}")
            route_err = validate_route_intent_against_binding(it, binding)
            if route_err is not None:
                return fail(f"route intent/binding mismatch for intent_id={intent_id}: {route_err}")
            # Authenticity anchor: the binding must pin the pre-state snapshot.
            # Without it a forged settlement could pin the CURRENT (drifted)
            # state and fill a route that the canonical pre-state snapshot would
            # not — snapshot-bound execution must fill only against pre-state.
            if not route_binding_pins_committed_snapshot_v1(binding, pre_pools):
                return fail(
                    "route fill binding does not pin the pre-state snapshot "
                    f"for intent_id={intent_id}"
                )

            replay = replay_route_legs_committed_v1(
                binding=binding,
                pools=replay_state.pools,
            )
            if not replay.ok:
                return fail(
                    f"route replay failed for intent_id={intent_id}: {replay.reject_reason}"
                )
            totals_err = route_totals_violation(it, replay)
            if totals_err is not None:
                return fail(f"route totals violation for intent_id={intent_id}: {totals_err}")

            if int(f.amount_in_filled or 0) != int(replay.total_amount_in):
                return fail(f"route amount_in_filled mismatch for intent_id={intent_id}")
            if int(f.amount_out_filled or 0) != int(replay.total_amount_out):
                return fail(f"route amount_out_filled mismatch for intent_id={intent_id}")
            if int(f.fee_paid or 0) != int(replay.total_fee_paid):
                return fail(f"route fee_paid mismatch for intent_id={intent_id}")

            try:
                applied = _apply_spot_replay_v1(
                    replay_state,
                    _SpotReplayDeltaBatchV1(
                        balance_deltas=tuple(
                            delta
                            for leg in replay.legs
                            for delta in (
                                BalanceDeltaV1(
                                    (sender, leg.asset_in),
                                    -leg.amount_in,
                                ),
                                BalanceDeltaV1(
                                    (recipient, leg.asset_out),
                                    leg.amount_out,
                                ),
                            )
                        ),
                        reserve_deltas=tuple(
                            delta
                            for leg in replay.legs
                            for delta in (
                                PoolReserveDeltaV1(
                                    leg.pool_id,
                                    leg.asset_in,
                                    leg.amount_in,
                                ),
                                PoolReserveDeltaV1(
                                    leg.pool_id,
                                    leg.asset_out,
                                    -leg.amount_out,
                                ),
                            )
                        ),
                        lp_deltas=(),
                        pool_creations=(),
                    ),
                )
                if isinstance(applied, _SpotReplayRejectV1):
                    raise ValueError(applied.text())
                replay_state = applied
            except (TypeError, ValueError) as exc:
                return fail(f"route apply error for intent_id={intent_id}: {exc}")

            for leg in replay.legs:
                bal_deltas.append(
                    BalanceDelta(
                        pubkey=sender, asset=leg.asset_in, delta_add=0, delta_sub=int(leg.amount_in)
                    )
                )
                bal_deltas.append(
                    BalanceDelta(
                        pubkey=recipient,
                        asset=leg.asset_out,
                        delta_add=int(leg.amount_out),
                        delta_sub=0,
                    )
                )
                res_deltas.append(
                    ReserveDelta(
                        pool_id=leg.pool_id,
                        asset=leg.asset_in,
                        delta_add=int(leg.amount_in),
                        delta_sub=0,
                    )
                )
                res_deltas.append(
                    ReserveDelta(
                        pool_id=leg.pool_id,
                        asset=leg.asset_out,
                        delta_add=0,
                        delta_sub=int(leg.amount_out),
                    )
                )
            continue

        pool_id = it.get_field("pool_id")
        if not isinstance(pool_id, str) or not pool_id:
            return fail(f"missing pool_id for intent_id={intent_id}")
        if pool_id not in replay_state.pools:
            return fail(f"pool not found for intent_id={intent_id}: {pool_id}")
        pool = replay_state.pools[pool_id]

        if it.kind in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
            asset_in = it.get_field("asset_in")
            asset_out = it.get_field("asset_out")
            if not isinstance(asset_in, str) or not isinstance(asset_out, str):
                return fail(f"invalid asset_in/out for intent_id={intent_id}")
            if pool.status.member_ordinal != POOL_STATUS_ACTIVE_MEMBER_ORDINAL_V1:
                return fail(
                    f"pool not active for intent_id={intent_id}: {_pool_status_text_v1(pool)}"
                )
            if {asset_in, asset_out} != {pool.asset0, pool.asset1} or asset_in == asset_out:
                return fail(f"swap asset mismatch for intent_id={intent_id}")
            if quote_pool_fp is not None:
                actual_pool_fp = pool_state_fingerprint_committed_v1(pool)
                if actual_pool_fp != quote_pool_fp:
                    return fail(
                        _quote_binding_error(
                            "quote receipt pool snapshot mismatch",
                            **_quote_binding_context(it),
                            actual_pool_fingerprint=actual_pool_fp,
                        )
                    )

            # CoW netting semantics (optional): direct user-to-user swap, no pool reserve changes.
            if f.reason == "COW_NETTED":
                if not allow_cow_netting:
                    return fail(f"COW_NETTED not allowed for intent_id={intent_id}")
                if it.kind != IntentKind.SWAP_EXACT_IN:
                    return fail(
                        f"COW_NETTED only supported for SWAP_EXACT_IN: intent_id={intent_id}"
                    )
                amount_in = it.get_field("amount_in")
                min_out = it.get_field("min_amount_out", 0)
                if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
                    return fail(f"invalid amount_in for intent_id={intent_id}")
                if not isinstance(min_out, int) or isinstance(min_out, bool) or min_out < 0:
                    return fail(f"invalid min_amount_out for intent_id={intent_id}")
                if int(f.fee_paid or 0) != 0:
                    return fail(f"COW_NETTED fee_paid must be 0: intent_id={intent_id}")
                if int(f.amount_in_filled or 0) != int(amount_in):
                    return fail(f"COW_NETTED amount_in_filled mismatch: intent_id={intent_id}")
                out_amt = int(f.amount_out_filled or 0)
                if out_amt < int(min_out):
                    return fail(f"COW_NETTED slippage: intent_id={intent_id}")
                try:
                    applied = _apply_spot_replay_v1(
                        replay_state,
                        _SpotReplayDeltaBatchV1(
                            balance_deltas=(
                                BalanceDeltaV1((sender, asset_in), -amount_in),
                                BalanceDeltaV1((recipient, asset_out), out_amt),
                            ),
                            reserve_deltas=(),
                            lp_deltas=(),
                            pool_creations=(),
                        ),
                    )
                    if isinstance(applied, _SpotReplayRejectV1):
                        raise ValueError(applied.text())
                    replay_state = applied
                except (TypeError, ValueError) as exc:
                    return fail(f"COW_NETTED apply error for intent_id={intent_id}: {exc}")

                bal_deltas.append(
                    BalanceDelta(
                        pubkey=sender, asset=asset_in, delta_add=0, delta_sub=int(amount_in)
                    )
                )
                bal_deltas.append(
                    BalanceDelta(pubkey=recipient, asset=asset_out, delta_add=out_amt, delta_sub=0)
                )
                continue

            if asset_in == pool.asset0 and asset_out == pool.asset1:
                reserve_in = int(pool.reserve0)
                reserve_out = int(pool.reserve1)
                dir_is_0_to_1 = True
            else:
                reserve_in = int(pool.reserve1)
                reserve_out = int(pool.reserve0)
                dir_is_0_to_1 = False

            if mode == _MODE_STRONG_PROOF_CARRYING:
                if f.reserve_in_before is None or f.reserve_out_before is None:
                    return fail(f"missing swap witness reserves for intent_id={intent_id}")
                if int(f.reserve_in_before) != int(reserve_in) or int(f.reserve_out_before) != int(
                    reserve_out
                ):
                    return fail(f"swap witness reserve mismatch for intent_id={intent_id}")

            if it.kind == IntentKind.SWAP_EXACT_IN:
                amount_in = it.get_field("amount_in")
                min_out = it.get_field("min_amount_out", 0)
                if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
                    return fail(f"invalid amount_in for intent_id={intent_id}")
                if not isinstance(min_out, int) or isinstance(min_out, bool) or min_out < 0:
                    return fail(f"invalid min_amount_out for intent_id={intent_id}")

                if int(f.amount_in_filled or 0) != int(amount_in):
                    return fail(f"swap amount_in_filled mismatch for intent_id={intent_id}")

                try:
                    if int(protocol_fee_share_bps):
                        if pool.curve_tag != CURVE_TAG_CPMM:
                            return fail(f"protocol fee unsupported for curve intent_id={intent_id}")
                        quote = swap_exact_in_with_protocol_fee(
                            reserve_in=int(reserve_in),
                            reserve_out=int(reserve_out),
                            amount_in=int(amount_in),
                            fee_bps=int(pool.fee_bps),
                            protocol_fee_share_bps=int(protocol_fee_share_bps),
                        )
                        amount_out = int(quote.amount_out)
                        new_in = int(quote.new_reserve_in)
                        new_out = int(quote.new_reserve_out)
                        protocol_fee = int(quote.protocol_fee)
                    else:
                        amount_out, (new_in, new_out) = swap_exact_in_for_committed_pool_v1(
                            pool,
                            reserve_in=int(reserve_in),
                            reserve_out=int(reserve_out),
                            amount_in=int(amount_in),
                        )
                        protocol_fee = 0
                except (ArithmeticError, TypeError, ValueError) as exc:
                    return fail(f"swap_exact_in kernel error for intent_id={intent_id}: {exc}")

                if int(f.amount_out_filled or 0) != int(amount_out):
                    return fail(f"swap amount_out_filled mismatch for intent_id={intent_id}")
                if int(amount_out) < int(min_out):
                    return fail(f"swap slippage for intent_id={intent_id}")

                fee = compute_fee_total(int(amount_in), int(pool.fee_bps))
                if int(f.fee_paid or 0) != int(fee):
                    return fail(f"swap fee_paid mismatch for intent_id={intent_id}")
                if int(f.protocol_fee_paid or 0) != int(protocol_fee):
                    return fail(f"swap protocol_fee_paid mismatch for intent_id={intent_id}")

                try:
                    applied = _apply_pool_swap_spot_v1(
                        replay_state,
                        _PoolSwapApplyV1(
                            pool_id=pool_id,
                            sender=sender,
                            recipient=recipient,
                            asset_in=asset_in,
                            asset_out=asset_out,
                            amount_in=amount_in,
                            amount_out=amount_out,
                            protocol_fee=protocol_fee,
                            protocol_fee_recipient=protocol_fee_recipient_pubkey,
                        ),
                    )
                    if isinstance(applied, _SpotReplayRejectV1):
                        raise ValueError(applied.text())
                    replay_state = applied
                    if not _pool_reserves_match_quote_v1(
                        replay_state.pools[pool_id],
                        dir_is_0_to_1,
                        new_in,
                        new_out,
                    ):
                        raise ValueError("spot transition disagrees with swap kernel reserves")
                except (TypeError, ValueError) as exc:
                    return fail(f"swap apply error for intent_id={intent_id}: {exc}")

                delta_error = _append_pool_swap_deltas(
                    pool_id=pool_id,
                    sender=sender,
                    recipient=recipient,
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_in=amount_in,
                    amount_out=amount_out,
                    protocol_fee=protocol_fee,
                    protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
                    bal_deltas=bal_deltas,
                    res_deltas=res_deltas,
                )
                if delta_error is not None:
                    return fail(f"{delta_error} for intent_id={intent_id}")
                continue

            # SWAP_EXACT_OUT
            amount_out_req = it.get_field("amount_out")
            max_in = it.get_field("max_amount_in")
            if (
                not isinstance(amount_out_req, int)
                or isinstance(amount_out_req, bool)
                or amount_out_req <= 0
            ):
                return fail(f"invalid amount_out for intent_id={intent_id}")
            if not isinstance(max_in, int) or isinstance(max_in, bool) or max_in < 0:
                return fail(f"invalid max_amount_in for intent_id={intent_id}")

            if int(f.amount_out_filled or 0) != int(amount_out_req):
                return fail(f"swap amount_out_filled mismatch for intent_id={intent_id}")

            try:
                if int(protocol_fee_share_bps):
                    if pool.curve_tag != CURVE_TAG_CPMM:
                        return fail(f"protocol fee unsupported for curve intent_id={intent_id}")
                    quote = quote_cpmm_swap_exact_out(
                        reserve_in=int(reserve_in),
                        reserve_out=int(reserve_out),
                        amount_out=int(amount_out_req),
                        fee_bps=int(pool.fee_bps),
                        protocol_fee_share_bps=int(protocol_fee_share_bps),
                    )
                    amount_in_req = int(quote.amount_in)
                    new_in = int(quote.reserve_in_after)
                    new_out = int(quote.reserve_out_after)
                    protocol_fee = int(quote.protocol_fee_paid)
                else:
                    amount_in_req, (new_in, new_out) = swap_exact_out_for_committed_pool_v1(
                        pool,
                        reserve_in=int(reserve_in),
                        reserve_out=int(reserve_out),
                        amount_out=int(amount_out_req),
                    )
                    protocol_fee = 0
            except (ArithmeticError, TypeError, ValueError) as exc:
                return fail(f"swap_exact_out kernel error for intent_id={intent_id}: {exc}")

            if int(f.amount_in_filled or 0) != int(amount_in_req):
                return fail(f"swap amount_in_filled mismatch for intent_id={intent_id}")
            if int(amount_in_req) > int(max_in):
                return fail(f"swap slippage for intent_id={intent_id}")

            fee = compute_fee_total(int(amount_in_req), int(pool.fee_bps))
            if int(f.fee_paid or 0) != int(fee):
                return fail(f"swap fee_paid mismatch for intent_id={intent_id}")
            if int(f.protocol_fee_paid or 0) != int(protocol_fee):
                return fail(f"swap protocol_fee_paid mismatch for intent_id={intent_id}")

            try:
                applied = _apply_pool_swap_spot_v1(
                    replay_state,
                    _PoolSwapApplyV1(
                        pool_id=pool_id,
                        sender=sender,
                        recipient=recipient,
                        asset_in=asset_in,
                        asset_out=asset_out,
                        amount_in=amount_in_req,
                        amount_out=amount_out_req,
                        protocol_fee=protocol_fee,
                        protocol_fee_recipient=protocol_fee_recipient_pubkey,
                    ),
                )
                if isinstance(applied, _SpotReplayRejectV1):
                    raise ValueError(applied.text())
                replay_state = applied
                if not _pool_reserves_match_quote_v1(
                    replay_state.pools[pool_id],
                    dir_is_0_to_1,
                    new_in,
                    new_out,
                ):
                    raise ValueError("spot transition disagrees with swap kernel reserves")
            except (TypeError, ValueError) as exc:
                return fail(f"swap apply error for intent_id={intent_id}: {exc}")

            delta_error = _append_pool_swap_deltas(
                pool_id=pool_id,
                sender=sender,
                recipient=recipient,
                asset_in=asset_in,
                asset_out=asset_out,
                amount_in=amount_in_req,
                amount_out=amount_out_req,
                protocol_fee=protocol_fee,
                protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
                bal_deltas=bal_deltas,
                res_deltas=res_deltas,
            )
            if delta_error is not None:
                return fail(f"{delta_error} for intent_id={intent_id}")
            continue

        if it.kind == IntentKind.ADD_LIQUIDITY:
            if pool.status.member_ordinal != POOL_STATUS_ACTIVE_MEMBER_ORDINAL_V1:
                return fail(
                    f"pool not active for intent_id={intent_id}: {_pool_status_text_v1(pool)}"
                )
            amount0_desired = it.get_field("amount0_desired")
            amount1_desired = it.get_field("amount1_desired")
            amount0_min = it.get_field("amount0_min", 0)
            amount1_min = it.get_field("amount1_min", 0)
            if any(v is None for v in (amount0_desired, amount1_desired)):
                return fail(f"missing ADD_LIQUIDITY fields for intent_id={intent_id}")
            if not is_strict_int(amount0_desired) or amount0_desired <= 0:
                return fail(f"invalid amount0_desired for intent_id={intent_id}")
            if not is_strict_int(amount1_desired) or amount1_desired <= 0:
                return fail(f"invalid amount1_desired for intent_id={intent_id}")
            if not is_strict_int(amount0_min) or amount0_min < 0:
                return fail(f"invalid amount0_min for intent_id={intent_id}")
            if not is_strict_int(amount1_min) or amount1_min < 0:
                return fail(f"invalid amount1_min for intent_id={intent_id}")

            try:
                amount0_used, amount1_used, lp_minted = add_liquidity_for_committed_pool_v1(
                    pool,
                    AddLiquidityKernelInputV1(
                        amount0_desired=amount0_desired,
                        amount1_desired=amount1_desired,
                        amount0_min=amount0_min,
                        amount1_min=amount1_min,
                    ),
                )
            except (ArithmeticError, TypeError, ValueError) as exc:
                return fail(f"ADD_LIQUIDITY computation error for intent_id={intent_id}: {exc}")

            if int(f.amount0_used or 0) != int(amount0_used):
                return fail(f"ADD_LIQUIDITY fill.amount0_used mismatch for intent_id={intent_id}")
            if int(f.amount1_used or 0) != int(amount1_used):
                return fail(f"ADD_LIQUIDITY fill.amount1_used mismatch for intent_id={intent_id}")
            if int(f.lp_minted or 0) != int(lp_minted):
                return fail(f"ADD_LIQUIDITY fill.lp_minted mismatch for intent_id={intent_id}")

            try:
                applied = _apply_spot_replay_v1(
                    replay_state,
                    _SpotReplayDeltaBatchV1(
                        balance_deltas=(
                            BalanceDeltaV1((sender, pool.asset0), -amount0_used),
                            BalanceDeltaV1((sender, pool.asset1), -amount1_used),
                        ),
                        reserve_deltas=(
                            PoolReserveDeltaV1(pool_id, pool.asset0, amount0_used),
                            PoolReserveDeltaV1(pool_id, pool.asset1, amount1_used),
                        ),
                        lp_deltas=(LPPositionDeltaV1((recipient, pool_id), lp_minted),),
                        pool_creations=(),
                    ),
                )
                if isinstance(applied, _SpotReplayRejectV1):
                    raise ValueError(applied.text())
                candidate_pool = applied.pools[pool_id]
                expected_pool_values = (
                    pool.reserve0 + amount0_used,
                    pool.reserve1 + amount1_used,
                    pool.lp_supply + lp_minted,
                )
                if (
                    candidate_pool.reserve0,
                    candidate_pool.reserve1,
                    candidate_pool.lp_supply,
                ) != expected_pool_values:
                    raise ValueError("spot transition disagrees with liquidity kernel")
                replay_state = applied
            except (TypeError, ValueError) as exc:
                return fail(f"ADD_LIQUIDITY apply error for intent_id={intent_id}: {exc}")

            bal_deltas.append(
                BalanceDelta(
                    pubkey=sender, asset=pool.asset0, delta_add=0, delta_sub=int(amount0_used)
                )
            )
            bal_deltas.append(
                BalanceDelta(
                    pubkey=sender, asset=pool.asset1, delta_add=0, delta_sub=int(amount1_used)
                )
            )
            res_deltas.append(
                ReserveDelta(
                    pool_id=pool_id, asset=pool.asset0, delta_add=int(amount0_used), delta_sub=0
                )
            )
            res_deltas.append(
                ReserveDelta(
                    pool_id=pool_id, asset=pool.asset1, delta_add=int(amount1_used), delta_sub=0
                )
            )
            lp_deltas.append(
                LPDelta(pubkey=recipient, pool_id=pool_id, delta_add=int(lp_minted), delta_sub=0)
            )
            continue

        if it.kind == IntentKind.REMOVE_LIQUIDITY:
            if pool.status.member_ordinal != POOL_STATUS_ACTIVE_MEMBER_ORDINAL_V1:
                return fail(
                    f"pool not active for intent_id={intent_id}: {_pool_status_text_v1(pool)}"
                )
            lp_amount = it.get_field("lp_amount")
            amount0_min = it.get_field("amount0_min", 0)
            amount1_min = it.get_field("amount1_min", 0)
            if lp_amount is None:
                return fail(f"missing REMOVE_LIQUIDITY lp_amount for intent_id={intent_id}")
            if not is_strict_int(lp_amount) or lp_amount <= 0:
                return fail(f"invalid lp_amount for intent_id={intent_id}")
            if not is_strict_int(amount0_min) or amount0_min < 0:
                return fail(f"invalid amount0_min for intent_id={intent_id}")
            if not is_strict_int(amount1_min) or amount1_min < 0:
                return fail(f"invalid amount1_min for intent_id={intent_id}")

            try:
                amount0_out, amount1_out = remove_liquidity_for_committed_pool_v1(
                    pool,
                    RemoveLiquidityKernelInputV1(
                        lp_amount=lp_amount,
                        amount0_min=amount0_min,
                        amount1_min=amount1_min,
                    ),
                )
            except (ArithmeticError, TypeError, ValueError) as exc:
                return fail(f"REMOVE_LIQUIDITY computation error for intent_id={intent_id}: {exc}")

            if int(f.lp_burned or 0) != int(lp_amount):
                return fail(f"REMOVE_LIQUIDITY fill.lp_burned mismatch for intent_id={intent_id}")
            if int(f.amount0_out or 0) != int(amount0_out):
                return fail(f"REMOVE_LIQUIDITY fill.amount0_out mismatch for intent_id={intent_id}")
            if int(f.amount1_out or 0) != int(amount1_out):
                return fail(f"REMOVE_LIQUIDITY fill.amount1_out mismatch for intent_id={intent_id}")

            try:
                balance_deltas_v1 = tuple(
                    delta
                    for asset, amount in (
                        (pool.asset0, amount0_out),
                        (pool.asset1, amount1_out),
                    )
                    if amount != 0
                    for delta in (BalanceDeltaV1((recipient, asset), amount),)
                )
                reserve_deltas_v1 = tuple(
                    delta
                    for asset, amount in (
                        (pool.asset0, amount0_out),
                        (pool.asset1, amount1_out),
                    )
                    if amount != 0
                    for delta in (PoolReserveDeltaV1(pool_id, asset, -amount),)
                )
                applied = _apply_spot_replay_v1(
                    replay_state,
                    _SpotReplayDeltaBatchV1(
                        balance_deltas=balance_deltas_v1,
                        reserve_deltas=reserve_deltas_v1,
                        lp_deltas=(LPPositionDeltaV1((sender, pool_id), -lp_amount),),
                        pool_creations=(),
                    ),
                )
                if isinstance(applied, _SpotReplayRejectV1):
                    raise ValueError(applied.text())
                candidate_pool = applied.pools[pool_id]
                expected_pool_values = (
                    pool.reserve0 - amount0_out,
                    pool.reserve1 - amount1_out,
                    pool.lp_supply - lp_amount,
                )
                if (
                    candidate_pool.reserve0,
                    candidate_pool.reserve1,
                    candidate_pool.lp_supply,
                ) != expected_pool_values:
                    raise ValueError("spot transition disagrees with liquidity kernel")
                replay_state = applied
            except (TypeError, ValueError) as exc:
                return fail(f"REMOVE_LIQUIDITY apply error for intent_id={intent_id}: {exc}")

            lp_deltas.append(
                LPDelta(pubkey=sender, pool_id=pool_id, delta_add=0, delta_sub=int(lp_amount))
            )
            bal_deltas.append(
                BalanceDelta(
                    pubkey=recipient, asset=pool.asset0, delta_add=int(amount0_out), delta_sub=0
                )
            )
            bal_deltas.append(
                BalanceDelta(
                    pubkey=recipient, asset=pool.asset1, delta_add=int(amount1_out), delta_sub=0
                )
            )
            res_deltas.append(
                ReserveDelta(
                    pool_id=pool_id, asset=pool.asset0, delta_add=0, delta_sub=int(amount0_out)
                )
            )
            res_deltas.append(
                ReserveDelta(
                    pool_id=pool_id, asset=pool.asset1, delta_add=0, delta_sub=int(amount1_out)
                )
            )
            continue

        return fail(f"unsupported intent kind for strong validation: {it.kind}")

    # Canonicalize and compare the settlement payloads.
    expected_balance = _aggregate_balance_deltas(bal_deltas)
    expected_reserve = _aggregate_reserve_deltas(res_deltas)
    expected_lp = _aggregate_lp_deltas(lp_deltas)

    ok, err = _check_canonical_deltas(settlement)
    if not ok:
        return _strong_reject_v1(err)

    if settlement.balance_deltas != expected_balance:
        return fail("balance_deltas mismatch vs replay")
    if settlement.reserve_deltas != expected_reserve:
        return fail("reserve_deltas mismatch vs replay")
    if settlement.lp_deltas != expected_lp:
        return fail("lp_deltas mismatch vs replay")

    exp_events_norm = expected_events
    got_events_norm = settlement.events or []
    if got_events_norm != exp_events_norm:
        return fail("events mismatch vs replay")

    # Each accepted replay step already proves balance, reserve, LP-position,
    # and derived LP-supply non-negativity over exact committed state. Global
    # asset conservation remains a batch property, especially for CoW fills
    # that exchange balances without touching reserves.
    conservation_error = _asset_conservation_error(
        expected_balance,
        expected_reserve,
    )
    if conservation_error is not None:
        return fail(f"legacy validation failed: {conservation_error}")

    if type(output_plan) is _ValidationOnlyOutputV1:
        return _StrongSettlementReplayAcceptedV1()

    exact_batch = _build_exact_spot_batch_v1(
        expected_balance,
        expected_reserve,
        expected_lp,
        exact_pool_creations,
    )
    if type(exact_batch) is StrongSettlementRejectV1:
        return exact_batch
    return _build_exact_spot_candidate_v1(
        pre_replay_state,
        replay_state,
        exact_batch,
        output_plan.context,
    )


def _append_pool_swap_deltas(
    *,
    pool_id: str,
    sender: PubKey,
    recipient: PubKey,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: int,
    amount_out: int,
    protocol_fee: int,
    protocol_fee_recipient_pubkey: Optional[PubKey],
    bal_deltas: List[BalanceDelta],
    res_deltas: List[ReserveDelta],
) -> Optional[str]:
    bal_deltas.append(
        BalanceDelta(pubkey=sender, asset=asset_in, delta_add=0, delta_sub=int(amount_in))
    )
    bal_deltas.append(
        BalanceDelta(pubkey=recipient, asset=asset_out, delta_add=int(amount_out), delta_sub=0)
    )
    if protocol_fee:
        if protocol_fee_recipient_pubkey is None:
            return "protocol_fee present without recipient"
        bal_deltas.append(
            BalanceDelta(
                pubkey=protocol_fee_recipient_pubkey,
                asset=asset_in,
                delta_add=int(protocol_fee),
                delta_sub=0,
            )
        )
    res_deltas.append(
        ReserveDelta(
            pool_id=pool_id,
            asset=asset_in,
            delta_add=int(amount_in) - int(protocol_fee),
            delta_sub=0,
        )
    )
    res_deltas.append(
        ReserveDelta(pool_id=pool_id, asset=asset_out, delta_add=0, delta_sub=int(amount_out))
    )
    return None


def _aggregate_balance_deltas(deltas: List[BalanceDelta]) -> List[BalanceDelta]:
    acc: Dict[Tuple[PubKey, AssetId], Tuple[int, int]] = {}
    for d in deltas:
        key = (d.pubkey, d.asset)
        add_prev, sub_prev = acc.get(key, (0, 0))
        acc[key] = (int(add_prev) + int(d.delta_add), int(sub_prev) + int(d.delta_sub))
    out: List[BalanceDelta] = []
    for key in sorted(acc.keys()):
        delta_add, delta_sub = acc[key]
        if delta_add == 0 and delta_sub == 0:
            continue
        out.append(
            BalanceDelta(
                pubkey=key[0], asset=key[1], delta_add=int(delta_add), delta_sub=int(delta_sub)
            )
        )
    return out


def _aggregate_reserve_deltas(deltas: List[ReserveDelta]) -> List[ReserveDelta]:
    acc: Dict[Tuple[str, AssetId], Tuple[int, int]] = {}
    for d in deltas:
        key = (d.pool_id, d.asset)
        add_prev, sub_prev = acc.get(key, (0, 0))
        acc[key] = (int(add_prev) + int(d.delta_add), int(sub_prev) + int(d.delta_sub))
    out: List[ReserveDelta] = []
    for key in sorted(acc.keys()):
        delta_add, delta_sub = acc[key]
        if delta_add == 0 and delta_sub == 0:
            continue
        out.append(
            ReserveDelta(
                pool_id=key[0], asset=key[1], delta_add=int(delta_add), delta_sub=int(delta_sub)
            )
        )
    return out


def _aggregate_lp_deltas(deltas: List[LPDelta]) -> List[LPDelta]:
    acc: Dict[Tuple[PubKey, str], Tuple[int, int]] = {}
    for d in deltas:
        key = (d.pubkey, d.pool_id)
        add_prev, sub_prev = acc.get(key, (0, 0))
        acc[key] = (int(add_prev) + int(d.delta_add), int(sub_prev) + int(d.delta_sub))
    out: List[LPDelta] = []
    for key in sorted(acc.keys()):
        delta_add, delta_sub = acc[key]
        if delta_add == 0 and delta_sub == 0:
            continue
        out.append(
            LPDelta(
                pubkey=key[0], pool_id=key[1], delta_add=int(delta_add), delta_sub=int(delta_sub)
            )
        )
    return out


def _asset_conservation_error(
    balance_deltas: List[BalanceDelta],
    reserve_deltas: List[ReserveDelta],
) -> Optional[str]:
    net_by_asset: Dict[AssetId, int] = {}
    for balance_delta in balance_deltas:
        net_by_asset[balance_delta.asset] = (
            net_by_asset.get(balance_delta.asset, 0) + balance_delta.net_delta()
        )
    for reserve_delta in reserve_deltas:
        net_by_asset[reserve_delta.asset] = (
            net_by_asset.get(reserve_delta.asset, 0) + reserve_delta.net_delta()
        )
    for asset in sorted(net_by_asset):
        net = net_by_asset[asset]
        if net != 0:
            return f"Asset conservation violation: {asset}, net_delta = {net}"
    return None


def _check_canonical_deltas(settlement: Settlement) -> Tuple[bool, Optional[str]]:
    # Ensure deltas are canonical (one entry per key, sorted, and with non-negative fields).
    def _check_unique_sorted(keys: List[Tuple], what: str) -> Tuple[bool, Optional[str]]:
        if keys != sorted(keys):
            return False, f"{what} not sorted canonically"
        if len(keys) != len(set(keys)):
            return False, f"{what} contains duplicate keys"
        return True, None

    # Balance deltas
    bal_keys: List[Tuple[PubKey, AssetId]] = []
    for balance_delta in settlement.balance_deltas:
        if (
            not isinstance(balance_delta.delta_add, int)
            or isinstance(balance_delta.delta_add, bool)
            or balance_delta.delta_add < 0
        ):
            return False, "balance_deltas contains invalid delta_add"
        if (
            not isinstance(balance_delta.delta_sub, int)
            or isinstance(balance_delta.delta_sub, bool)
            or balance_delta.delta_sub < 0
        ):
            return False, "balance_deltas contains invalid delta_sub"
        if balance_delta.delta_add == 0 and balance_delta.delta_sub == 0:
            return False, "balance_deltas contains a zero entry"
        bal_keys.append((balance_delta.pubkey, balance_delta.asset))
    ok, err = _check_unique_sorted(bal_keys, "balance_deltas")
    if not ok:
        return ok, err

    # Reserve deltas
    res_keys: List[Tuple[str, AssetId]] = []
    for reserve_delta in settlement.reserve_deltas:
        if (
            not isinstance(reserve_delta.delta_add, int)
            or isinstance(reserve_delta.delta_add, bool)
            or reserve_delta.delta_add < 0
        ):
            return False, "reserve_deltas contains invalid delta_add"
        if (
            not isinstance(reserve_delta.delta_sub, int)
            or isinstance(reserve_delta.delta_sub, bool)
            or reserve_delta.delta_sub < 0
        ):
            return False, "reserve_deltas contains invalid delta_sub"
        if reserve_delta.delta_add == 0 and reserve_delta.delta_sub == 0:
            return False, "reserve_deltas contains a zero entry"
        res_keys.append((reserve_delta.pool_id, reserve_delta.asset))
    ok, err = _check_unique_sorted(res_keys, "reserve_deltas")
    if not ok:
        return ok, err

    # LP deltas
    lp_keys: List[Tuple[PubKey, str]] = []
    for lp_delta in settlement.lp_deltas:
        if (
            not isinstance(lp_delta.delta_add, int)
            or isinstance(lp_delta.delta_add, bool)
            or lp_delta.delta_add < 0
        ):
            return False, "lp_deltas contains invalid delta_add"
        if (
            not isinstance(lp_delta.delta_sub, int)
            or isinstance(lp_delta.delta_sub, bool)
            or lp_delta.delta_sub < 0
        ):
            return False, "lp_deltas contains invalid delta_sub"
        if lp_delta.delta_add == 0 and lp_delta.delta_sub == 0:
            return False, "lp_deltas contains a zero entry"
        lp_keys.append((lp_delta.pubkey, lp_delta.pool_id))
    ok, err = _check_unique_sorted(lp_keys, "lp_deltas")
    if not ok:
        return ok, err

    return True, None
