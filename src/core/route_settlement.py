"""
Atomic route settlement (split-routing) core.

A RouteIntent binds ONE signature to ONE verified route quote receipt covering
ALL of the receipt's legs. Settlement is atomic by construction:

    every quoted leg validates + replays exactly -> the route fills
    any leg fails                                -> the whole route REJECTS,
                                                    no pool or balance change

Semantics (snapshot-bound, exact-quote execution — the same contract as the
existing single-swap `quote_pool_fingerprint` binding):
  - The receipt pins each referenced pool's full state via
    `pool_state_fingerprint`. Engine witness validation verifies the receipt
    against the pre-batch pools (`verify_route_quote_receipt`).
  - At clearing/validation time the fingerprints are re-checked against the
    CURRENT local replay state, then every leg's quoted amounts are re-derived
    with the verified swap kernels and must match EXACTLY. Any drift (e.g. an
    earlier route in the same batch moved a shared pool) deterministically
    rejects the route with no state change.

Scope (v1): each receipt leg must have exactly ONE hop (parallel split
routing). Multi-hop legs are rejected fail-closed at binding resolution.

This module is pure (functional core). Callers (batch clearing, the strong
validator) own state application; `replay_route_legs` only reads pool state
and returns the post-reserves the caller may commit.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, List, Mapping, Optional, Tuple, TypeAlias, cast

from ..state.intents import Intent, IntentKind
from ..state.owned_collections import OwnedMapV1
from ..state.pools import PoolState, PoolStatus
from ..state.state_snapshot_values import (
    FCIS_STATE_SCHEMA_REVISION_V1,
    POOL_MAP_SCHEMA_ID_V1,
    POOL_STATUS_ACTIVE_MEMBER_ORDINAL_V1,
    CommittedPoolStateV1,
)
from .amm_dispatch import (
    swap_exact_in_for_committed_pool_v1,
    swap_exact_in_for_pool,
    swap_exact_out_for_committed_pool_v1,
    swap_exact_out_for_pool,
)
from .cpmm import compute_fee_total
from .domain_limits import is_strict_int
from .quote_receipts import (
    pool_state_fingerprint,
    pool_state_fingerprint_committed_v1,
)

ROUTE_KIND_EXACT_IN = "exact_in"
ROUTE_KIND_EXACT_OUT = "exact_out"

# Engine-internal intent fields carrying the resolved binding from the engine
# witness validation to the strong validator. They are reserved: user-supplied
# values are rejected at the engine boundary and the strong validator only
# accepts them on the validated engine path.
ROUTE_LEGS_FIELD = "route_legs"
ROUTE_POOL_FINGERPRINTS_FIELD = "route_pool_fingerprints"
ROUTE_RESERVED_FIELDS = (ROUTE_LEGS_FIELD, ROUTE_POOL_FINGERPRINTS_FIELD)

# Stable reject codes (Fill.reason) for route clearing.
ROUTE_REJECT_BINDING_MISSING = "ROUTE_BINDING_MISSING"
ROUTE_REJECT_INVALID_PARAMS = "INVALID_PARAMS"
ROUTE_REJECT_POOL_NOT_FOUND = "POOL_NOT_FOUND"
ROUTE_REJECT_POOL_NOT_ACTIVE = "POOL_NOT_ACTIVE"
ROUTE_REJECT_POOL_STATE_DRIFT = "ROUTE_POOL_STATE_DRIFT"
ROUTE_REJECT_INSUFFICIENT_BALANCE = "INSUFFICIENT_BALANCE"
ROUTE_REJECT_LEG_QUOTE_MISMATCH = "ROUTE_LEG_QUOTE_MISMATCH"
ROUTE_REJECT_SLIPPAGE = "SLIPPAGE"

_ROUTE_INTENT_KINDS = (IntentKind.ROUTE_EXACT_IN, IntentKind.ROUTE_EXACT_OUT)

_PoolValueV1: TypeAlias = PoolState | CommittedPoolStateV1
_PoolMapV1: TypeAlias = Mapping[str, _PoolValueV1]


def _require_committed_pool_map_v1(
    pools: object,
) -> OwnedMapV1[str, CommittedPoolStateV1]:
    if type(pools) is not OwnedMapV1:
        raise TypeError("pools must be an exact committed pool map")
    exact_pools = cast(OwnedMapV1[str, CommittedPoolStateV1], pools)
    if (
        exact_pools.schema_revision != FCIS_STATE_SCHEMA_REVISION_V1
        or exact_pools.schema_id != POOL_MAP_SCHEMA_ID_V1
    ):
        raise TypeError("committed pool map schema metadata mismatch")
    return exact_pools


def _pool_is_active_v1(pool: _PoolValueV1) -> bool:
    if type(pool) is CommittedPoolStateV1:
        return pool.status.member_ordinal == POOL_STATUS_ACTIVE_MEMBER_ORDINAL_V1
    return pool.status == PoolStatus.ACTIVE


def _pool_fingerprint_v1(pool: _PoolValueV1) -> str:
    if type(pool) is CommittedPoolStateV1:
        return pool_state_fingerprint_committed_v1(pool)
    return pool_state_fingerprint(pool)


def _swap_exact_in_for_route_pool_v1(
    pool: _PoolValueV1,
    *,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
) -> tuple[int, tuple[int, int]]:
    if type(pool) is CommittedPoolStateV1:
        return swap_exact_in_for_committed_pool_v1(
            pool,
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_in=amount_in,
        )
    return swap_exact_in_for_pool(
        pool,
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
    )


def _swap_exact_out_for_route_pool_v1(
    pool: _PoolValueV1,
    *,
    reserve_in: int,
    reserve_out: int,
    amount_out: int,
) -> tuple[int, tuple[int, int]]:
    if type(pool) is CommittedPoolStateV1:
        return swap_exact_out_for_committed_pool_v1(
            pool,
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_out=amount_out,
        )
    return swap_exact_out_for_pool(
        pool,
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=amount_out,
    )


def is_route_intent_kind(kind: IntentKind) -> bool:
    return kind in _ROUTE_INTENT_KINDS


def route_kind_for_intent(intent: Intent) -> Optional[str]:
    if intent.kind == IntentKind.ROUTE_EXACT_IN:
        return ROUTE_KIND_EXACT_IN
    if intent.kind == IntentKind.ROUTE_EXACT_OUT:
        return ROUTE_KIND_EXACT_OUT
    return None


@dataclass(frozen=True)
class RouteLegBinding:
    """One single-hop leg of a verified route quote receipt."""

    pool_id: str
    asset_in: str
    asset_out: str
    amount_in: int
    amount_out: int


@dataclass(frozen=True)
class RouteBinding:
    """
    Resolved, receipt-derived route plan.

    Built by the engine from an already-verified quote receipt
    (`verify_route_quote_receipt` MUST pass first); re-parsed and re-validated
    from intent fields by the strong validator (untrusted input there).
    """

    kind: str  # "exact_in" | "exact_out"
    asset_in: str
    asset_out: str
    total_amount_in: int
    total_amount_out: int
    legs: Tuple[RouteLegBinding, ...]
    pool_fingerprints: Mapping[str, str]


def _require_non_empty_str(value: Any) -> Optional[str]:
    if not isinstance(value, str) or not value:
        return None
    return value


def _require_positive_int(value: Any) -> Optional[int]:
    if not is_strict_int(value) or int(value) <= 0:
        return None
    return int(value)


def resolve_route_binding_from_receipt(
    receipt: object,
) -> Tuple[Optional[RouteBinding], Optional[str]]:
    """
    Resolve a RouteBinding from a VERIFIED quote receipt.

    The caller must have already run `verify_route_quote_receipt` on the
    receipt; this function still validates shape fail-closed (it never trusts),
    and additionally enforces the v1 route scope: single-hop legs only.

    Returns (binding, None) or (None, error_code).
    """
    if not isinstance(receipt, Mapping):
        return None, "route_receipt_not_object"
    body = receipt.get("body")
    if not isinstance(body, Mapping):
        return None, "route_receipt_missing_body"

    kind = str(body.get("kind", "")).strip().lower()
    if kind not in (ROUTE_KIND_EXACT_IN, ROUTE_KIND_EXACT_OUT):
        return None, "route_receipt_bad_kind"

    asset_in = _require_non_empty_str(body.get("asset_in"))
    asset_out = _require_non_empty_str(body.get("asset_out"))
    if asset_in is None or asset_out is None or asset_in == asset_out:
        return None, "route_receipt_bad_assets"

    total_amount_in = _require_positive_int(body.get("amount_in"))
    total_amount_out = _require_positive_int(body.get("amount_out"))
    if total_amount_in is None or total_amount_out is None:
        return None, "route_receipt_bad_totals"

    raw_legs = body.get("legs")
    if not isinstance(raw_legs, list) or not raw_legs:
        return None, "route_receipt_bad_legs"

    pools = body.get("pools")
    if not isinstance(pools, Mapping):
        return None, "route_receipt_bad_pools"

    legs: List[RouteLegBinding] = []
    used_pool_ids: List[str] = []
    sum_in = 0
    sum_out = 0
    for raw_leg in raw_legs:
        if not isinstance(raw_leg, Mapping):
            return None, "route_receipt_bad_leg"
        hops = raw_leg.get("hops")
        if not isinstance(hops, list) or not hops:
            return None, "route_receipt_bad_hops"
        if len(hops) != 1:
            # v1 scope: parallel split routing only.
            return None, "route_multi_hop_leg_unsupported"
        hop = hops[0]
        if not isinstance(hop, Mapping):
            return None, "route_receipt_bad_hop"

        pool_id = _require_non_empty_str(hop.get("pool_id"))
        hop_asset_in = _require_non_empty_str(hop.get("asset_in"))
        hop_asset_out = _require_non_empty_str(hop.get("asset_out"))
        amount_in = _require_positive_int(hop.get("amount_in"))
        amount_out = _require_positive_int(hop.get("amount_out"))
        if pool_id is None or hop_asset_in is None or hop_asset_out is None:
            return None, "route_receipt_bad_hop_fields"
        if amount_in is None or amount_out is None:
            return None, "route_receipt_bad_hop_amounts"
        # Single-hop legs must span the route endpoints exactly.
        if hop_asset_in != asset_in or hop_asset_out != asset_out:
            return None, "route_receipt_leg_endpoint_mismatch"

        leg_amount_in = _require_positive_int(raw_leg.get("amount_in"))
        leg_amount_out = _require_positive_int(raw_leg.get("amount_out"))
        if leg_amount_in != amount_in or leg_amount_out != amount_out:
            return None, "route_receipt_leg_amount_mismatch"

        legs.append(
            RouteLegBinding(
                pool_id=pool_id,
                asset_in=hop_asset_in,
                asset_out=hop_asset_out,
                amount_in=amount_in,
                amount_out=amount_out,
            )
        )
        if pool_id not in used_pool_ids:
            used_pool_ids.append(pool_id)
        sum_in += amount_in
        sum_out += amount_out

    if sum_in != total_amount_in or sum_out != total_amount_out:
        return None, "route_receipt_totals_mismatch"

    fingerprints: Dict[str, str] = {}
    for pool_id in used_pool_ids:
        fp = _require_non_empty_str(pools.get(pool_id))
        if fp is None:
            return None, "route_receipt_missing_pool_fingerprint"
        fingerprints[pool_id] = fp

    return (
        RouteBinding(
            kind=kind,
            asset_in=asset_in,
            asset_out=asset_out,
            total_amount_in=total_amount_in,
            total_amount_out=total_amount_out,
            legs=tuple(legs),
            pool_fingerprints=fingerprints,
        ),
        None,
    )


def route_binding_to_fields(binding: RouteBinding) -> Dict[str, Any]:
    """Serialize a binding into the engine-internal sanitized intent fields."""
    return {
        ROUTE_LEGS_FIELD: [
            {
                "pool_id": leg.pool_id,
                "asset_in": leg.asset_in,
                "asset_out": leg.asset_out,
                "amount_in": int(leg.amount_in),
                "amount_out": int(leg.amount_out),
            }
            for leg in binding.legs
        ],
        ROUTE_POOL_FINGERPRINTS_FIELD: dict(binding.pool_fingerprints),
    }


def parse_route_binding_fields(
    intent: Intent,
) -> Tuple[Optional[RouteBinding], Optional[str]]:
    """
    Parse a RouteBinding from (untrusted) sanitized intent fields.

    The strong validator uses this; everything is re-validated fail-closed.
    The intent's own route fields define kind/endpoints/totals; the leg list
    and fingerprints come from the engine-injected reserved fields.
    """
    kind = route_kind_for_intent(intent)
    if kind is None:
        return None, "not_a_route_intent"

    asset_in = _require_non_empty_str(intent.get_field("asset_in"))
    asset_out = _require_non_empty_str(intent.get_field("asset_out"))
    if asset_in is None or asset_out is None or asset_in == asset_out:
        return None, "route_intent_bad_assets"

    raw_legs = intent.get_field(ROUTE_LEGS_FIELD)
    if not isinstance(raw_legs, list) or not raw_legs:
        return None, "route_binding_missing_legs"
    raw_fps = intent.get_field(ROUTE_POOL_FINGERPRINTS_FIELD)
    if not isinstance(raw_fps, Mapping) or not raw_fps:
        return None, "route_binding_missing_fingerprints"

    legs: List[RouteLegBinding] = []
    used_pool_ids: List[str] = []
    sum_in = 0
    sum_out = 0
    for raw_leg in raw_legs:
        if not isinstance(raw_leg, Mapping):
            return None, "route_binding_bad_leg"
        pool_id = _require_non_empty_str(raw_leg.get("pool_id"))
        leg_asset_in = _require_non_empty_str(raw_leg.get("asset_in"))
        leg_asset_out = _require_non_empty_str(raw_leg.get("asset_out"))
        amount_in = _require_positive_int(raw_leg.get("amount_in"))
        amount_out = _require_positive_int(raw_leg.get("amount_out"))
        if pool_id is None or leg_asset_in is None or leg_asset_out is None:
            return None, "route_binding_bad_leg_fields"
        if amount_in is None or amount_out is None:
            return None, "route_binding_bad_leg_amounts"
        if leg_asset_in != asset_in or leg_asset_out != asset_out:
            return None, "route_binding_leg_endpoint_mismatch"
        if set(raw_leg.keys()) != {"pool_id", "asset_in", "asset_out", "amount_in", "amount_out"}:
            return None, "route_binding_unknown_leg_fields"
        legs.append(
            RouteLegBinding(
                pool_id=pool_id,
                asset_in=leg_asset_in,
                asset_out=leg_asset_out,
                amount_in=amount_in,
                amount_out=amount_out,
            )
        )
        if pool_id not in used_pool_ids:
            used_pool_ids.append(pool_id)
        sum_in += amount_in
        sum_out += amount_out

    fingerprints: Dict[str, str] = {}
    for pool_id, fp in raw_fps.items():
        pool_id_s = _require_non_empty_str(pool_id)
        fp_s = _require_non_empty_str(fp)
        if pool_id_s is None or fp_s is None:
            return None, "route_binding_bad_fingerprint_entry"
        fingerprints[pool_id_s] = fp_s
    if set(fingerprints.keys()) != set(used_pool_ids):
        return None, "route_binding_fingerprint_pool_mismatch"

    return (
        RouteBinding(
            kind=kind,
            asset_in=asset_in,
            asset_out=asset_out,
            total_amount_in=sum_in,
            total_amount_out=sum_out,
            legs=tuple(legs),
            pool_fingerprints=fingerprints,
        ),
        None,
    )


def validate_route_intent_against_binding(
    intent: Intent,
    binding: RouteBinding,
) -> Optional[str]:
    """
    Check the user's signed route fields against the resolved binding.

    Returns None when consistent, else a stable error code.
    """
    kind = route_kind_for_intent(intent)
    if kind is None or kind != binding.kind:
        return "route_kind_mismatch"

    if intent.get_field("asset_in") != binding.asset_in:
        return "route_asset_in_mismatch"
    if intent.get_field("asset_out") != binding.asset_out:
        return "route_asset_out_mismatch"

    leg_indices = intent.get_field("leg_indices")
    if not isinstance(leg_indices, list) or not leg_indices:
        return "route_leg_indices_missing"
    for idx in leg_indices:
        if not is_strict_int(idx) or int(idx) < 0:
            return "route_leg_indices_invalid"
    if list(leg_indices) != list(range(len(binding.legs))):
        return "route_leg_coverage_mismatch"

    recipient = intent.get_field("recipient", intent.sender_pubkey)
    if not isinstance(recipient, str) or not recipient:
        return "route_recipient_invalid"

    if kind == ROUTE_KIND_EXACT_IN:
        total_amount_in = intent.get_field("total_amount_in")
        total_min_amount_out = intent.get_field("total_min_amount_out")
        if not is_strict_int(total_amount_in) or int(total_amount_in) <= 0:
            return "route_total_amount_in_invalid"
        if not is_strict_int(total_min_amount_out) or int(total_min_amount_out) < 0:
            return "route_total_min_amount_out_invalid"
        if int(total_amount_in) != int(binding.total_amount_in):
            return "route_total_amount_in_mismatch"
        if int(total_min_amount_out) > int(binding.total_amount_out):
            return "route_min_out_unsatisfiable"
        return None

    total_amount_out = intent.get_field("total_amount_out")
    total_max_amount_in = intent.get_field("total_max_amount_in")
    if not is_strict_int(total_amount_out) or int(total_amount_out) <= 0:
        return "route_total_amount_out_invalid"
    if not is_strict_int(total_max_amount_in) or int(total_max_amount_in) < 0:
        return "route_total_max_amount_in_invalid"
    if int(total_amount_out) != int(binding.total_amount_out):
        return "route_total_amount_out_mismatch"
    if int(total_max_amount_in) < int(binding.total_amount_in):
        return "route_max_in_unsatisfiable"
    return None


def route_binding_pins_snapshot(
    binding: RouteBinding,
    pre_pools: Mapping[str, PoolState],
) -> bool:
    """
    Return True iff the binding's pinned pool fingerprints exactly match the
    PRE-STATE pools (batch start).

    An authentic binding is derived from a quote receipt that the engine
    verified against the pre-batch pools, so its fingerprints equal the
    pre-state fingerprints. This anchor lets the validator distinguish a
    GENUINE in-batch drift reject (binding pins pre-state, but an earlier
    intent moved the pool so the fingerprint no longer matches the CURRENT
    state) from a TAMPERED fingerprint (pins neither pre- nor current-state,
    forging a fake `ROUTE_POOL_STATE_DRIFT` to make a competing route win).
    """
    return _route_binding_pins_pool_map_v1(binding, pre_pools)


def route_binding_pins_committed_snapshot_v1(
    binding: RouteBinding,
    pre_pools: OwnedMapV1[str, CommittedPoolStateV1],
) -> bool:
    """Check a route binding against one exact committed pool snapshot."""

    return _route_binding_pins_pool_map_v1(
        binding,
        _require_committed_pool_map_v1(pre_pools),
    )


def _route_binding_pins_pool_map_v1(
    binding: RouteBinding,
    pre_pools: _PoolMapV1,
) -> bool:
    for pool_id in sorted(binding.pool_fingerprints):
        fingerprint = binding.pool_fingerprints[pool_id]
        pool = pre_pools.get(pool_id)
        if pool is None or _pool_fingerprint_v1(pool) != fingerprint:
            return False
    return True


@dataclass(frozen=True)
class RouteLegReplay:
    """Replayed leg result against the current local pool state."""

    pool_id: str
    asset_in: str
    asset_out: str
    amount_in: int
    amount_out: int
    fee_paid: int
    new_reserve0: int
    new_reserve1: int


@dataclass(frozen=True)
class RouteReplayResult:
    ok: bool
    reject_reason: Optional[str] = None
    legs: Tuple[RouteLegReplay, ...] = ()
    total_amount_in: int = 0
    total_amount_out: int = 0
    total_fee_paid: int = 0


def _route_pool_preflight_v1(
    binding: RouteBinding,
    pools: _PoolMapV1,
    ordered_pool_ids: tuple[str, ...],
) -> RouteReplayResult | None:
    for pool_id in ordered_pool_ids:
        pool = pools.get(pool_id)
        if pool is None:
            return RouteReplayResult(ok=False, reject_reason=ROUTE_REJECT_POOL_NOT_FOUND)
        if not _pool_is_active_v1(pool):
            return RouteReplayResult(ok=False, reject_reason=ROUTE_REJECT_POOL_NOT_ACTIVE)
        if _pool_fingerprint_v1(pool) != binding.pool_fingerprints[pool_id]:
            return RouteReplayResult(ok=False, reject_reason=ROUTE_REJECT_POOL_STATE_DRIFT)
    return None


def _initial_route_scratch_v1(
    pools: _PoolMapV1,
    ordered_pool_ids: tuple[str, ...],
) -> dict[str, tuple[int, int]]:
    return {
        pool_id: (int(pools[pool_id].reserve0), int(pools[pool_id].reserve1))
        for pool_id in ordered_pool_ids
    }


def _route_leg_reserves_v1(
    pool: _PoolValueV1,
    leg: RouteLegBinding,
    reserves: tuple[int, int],
) -> tuple[int, int, bool] | None:
    reserve0, reserve1 = reserves
    if leg.asset_in == pool.asset0 and leg.asset_out == pool.asset1:
        return reserve0, reserve1, True
    if leg.asset_in == pool.asset1 and leg.asset_out == pool.asset0:
        return reserve1, reserve0, False
    return None


def _replay_route_leg_v1(
    kind: str,
    pool: _PoolValueV1,
    leg: RouteLegBinding,
    reserves: tuple[int, int],
) -> RouteLegReplay | RouteReplayResult:
    oriented = _route_leg_reserves_v1(pool, leg, reserves)
    if oriented is None:
        return RouteReplayResult(ok=False, reject_reason=ROUTE_REJECT_INVALID_PARAMS)
    reserve_in, reserve_out, dir_is_0_to_1 = oriented

    try:
        if kind == ROUTE_KIND_EXACT_IN:
            quoted, (new_in, new_out) = _swap_exact_in_for_route_pool_v1(
                pool,
                reserve_in=reserve_in,
                reserve_out=reserve_out,
                amount_in=leg.amount_in,
            )
            expected_quote = leg.amount_out
        else:
            quoted, (new_in, new_out) = _swap_exact_out_for_route_pool_v1(
                pool,
                reserve_in=reserve_in,
                reserve_out=reserve_out,
                amount_out=leg.amount_out,
            )
            expected_quote = leg.amount_in
    except (ArithmeticError, TypeError, ValueError):
        return RouteReplayResult(ok=False, reject_reason=ROUTE_REJECT_LEG_QUOTE_MISMATCH)
    if quoted != expected_quote:
        return RouteReplayResult(ok=False, reject_reason=ROUTE_REJECT_LEG_QUOTE_MISMATCH)

    new_reserve0, new_reserve1 = (
        (int(new_in), int(new_out))
        if dir_is_0_to_1
        else (int(new_out), int(new_in))
    )
    return RouteLegReplay(
        pool_id=leg.pool_id,
        asset_in=leg.asset_in,
        asset_out=leg.asset_out,
        amount_in=leg.amount_in,
        amount_out=leg.amount_out,
        fee_paid=compute_fee_total(leg.amount_in, pool.fee_bps),
        new_reserve0=new_reserve0,
        new_reserve1=new_reserve1,
    )


def replay_route_legs(
    *,
    binding: RouteBinding,
    pools: Mapping[str, PoolState],
) -> RouteReplayResult:
    """
    Replay every leg of the binding against the CURRENT pool states.

    Pure: `pools` is read-only; per-leg post-reserves are returned for the
    caller to commit (or discard — atomicity is the caller's two-phase
    contract: replay everything first, apply only on full success).

    Checks, fail-closed, first failure wins:
      1. every referenced pool exists and is ACTIVE
      2. every referenced pool's CURRENT fingerprint matches the binding
         (snapshot binding — rejects in-batch drift deterministically)
      3. every leg's quoted amounts replay EXACTLY under the verified kernels,
         threading evolving reserves across legs that share a pool
    """
    return _replay_route_legs_for_pool_map_v1(binding=binding, pools=pools)


def replay_route_legs_committed_v1(
    *,
    binding: RouteBinding,
    pools: OwnedMapV1[str, CommittedPoolStateV1],
) -> RouteReplayResult:
    """Replay a route against one exact immutable committed pool map."""

    return _replay_route_legs_for_pool_map_v1(
        binding=binding,
        pools=_require_committed_pool_map_v1(pools),
    )


def _replay_route_legs_for_pool_map_v1(
    *,
    binding: RouteBinding,
    pools: _PoolMapV1,
) -> RouteReplayResult:
    # Phase 1: pool presence + status + snapshot fingerprints (vs current state).
    # Fingerprint maps are semantically unordered. Sorting gives one rejection
    # precedence independent of dict construction or collection internals.
    ordered_pool_ids = tuple(sorted(binding.pool_fingerprints))
    preflight = _route_pool_preflight_v1(binding, pools, ordered_pool_ids)
    if preflight is not None:
        return preflight

    # Phase 2: exact kernel replay on scratch reserves (thread across legs).
    scratch = _initial_route_scratch_v1(pools, ordered_pool_ids)

    replays: List[RouteLegReplay] = []
    for leg in binding.legs:
        pool = pools.get(leg.pool_id)
        if pool is None or leg.pool_id not in scratch:
            return RouteReplayResult(ok=False, reject_reason=ROUTE_REJECT_POOL_NOT_FOUND)
        replay = _replay_route_leg_v1(binding.kind, pool, leg, scratch[leg.pool_id])
        if isinstance(replay, RouteReplayResult):
            return replay
        replays.append(replay)
        scratch[leg.pool_id] = (replay.new_reserve0, replay.new_reserve1)

    return RouteReplayResult(
        ok=True,
        legs=tuple(replays),
        total_amount_in=sum(replay.amount_in for replay in replays),
        total_amount_out=sum(replay.amount_out for replay in replays),
        total_fee_paid=sum(replay.fee_paid for replay in replays),
    )


def route_totals_violation(
    intent: Intent,
    replay: RouteReplayResult,
) -> Optional[str]:
    """
    Final totals gate against the user's signed limits (defense-in-depth: the
    binding equality checks already imply these on the admitted path).

    Returns None when satisfied, else the stable SLIPPAGE reject code.
    """
    kind = route_kind_for_intent(intent)
    if kind == ROUTE_KIND_EXACT_IN:
        total_min_amount_out = intent.get_field("total_min_amount_out")
        if not is_strict_int(total_min_amount_out) or int(total_min_amount_out) < 0:
            return ROUTE_REJECT_INVALID_PARAMS
        if int(replay.total_amount_out) < int(total_min_amount_out):
            return ROUTE_REJECT_SLIPPAGE
        return None
    if kind == ROUTE_KIND_EXACT_OUT:
        total_max_amount_in = intent.get_field("total_max_amount_in")
        if not is_strict_int(total_max_amount_in) or int(total_max_amount_in) < 0:
            return ROUTE_REJECT_INVALID_PARAMS
        if int(replay.total_amount_in) > int(total_max_amount_in):
            return ROUTE_REJECT_SLIPPAGE
        return None
    return ROUTE_REJECT_INVALID_PARAMS
