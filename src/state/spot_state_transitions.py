"""Atomic exact spot-state transitions over committed FCIS values.

This module composes balance, pool, and LP leaf patches into one all-or-none
candidate. Pool LP-supply deltas are derived from the accepted LP-position
patch; callers cannot provide a contradictory supply change.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias, final

from .owned_collections import OwnedMapV1
from .pool_creation_transition import PoolCreationV1, build_committed_pool_creation_v1
from .snapshot_combinators import MAX_CANONICAL_BYTES_V1, MAX_COLLECTION_ITEMS_V1
from .state_snapshot_values import (
    CommittedBalanceTableV1,
    CommittedLPTableV1,
    CommittedPoolStateV1,
)
from .state_snapshots import (
    StateAdmissionError,
    snapshot_balance_table,
    snapshot_lp_table,
    snapshot_pool_map,
)
from .state_transitions import (
    BalanceDeltaV1,
    BalancePatchCodeV1,
    BalancePatchRejectV1,
    CanonicalBalancePatchV1,
    CanonicalLPPositionPatchV1,
    CanonicalPoolPatchV1,
    LPPositionDeltaV1,
    LPPositionPatchCodeV1,
    LPPositionPatchRejectV1,
    PoolPatchApplyOkV1,
    PoolPatchCodeV1,
    PoolPatchRejectV1,
    PoolReserveDeltaV1,
    PoolSupplyDeltaV1,
    PoolWriteV1,
    apply_balance_deltas_v1,
    apply_canonical_pool_patch_v1,
    apply_lp_position_deltas_v1,
    apply_pool_deltas_v1,
    build_canonical_pool_patch_v1,
    validate_balance_deltas_v1,
    validate_lp_position_deltas_v1,
    validate_pool_deltas_v1,
)

SpotTransitionRejectV1: TypeAlias = (
    BalancePatchRejectV1 | LPPositionPatchRejectV1 | PoolPatchRejectV1
)


@final
@dataclass(frozen=True, slots=True)
class SpotTransitionOkV1:
    """One complete immutable spot candidate and its canonical leaf patches."""

    balances: CommittedBalanceTableV1
    pools: OwnedMapV1[str, CommittedPoolStateV1]
    lp_balances: CommittedLPTableV1
    balance_patch: CanonicalBalancePatchV1 | None
    pool_patch: CanonicalPoolPatchV1 | None
    lp_patch: CanonicalLPPositionPatchV1 | None

    def __post_init__(self) -> None:
        if type(self.balances) is not CommittedBalanceTableV1:
            raise TypeError("spot balances must be an exact committed table")
        if type(self.pools) is not OwnedMapV1:
            raise TypeError("spot pools must be an exact owned map")
        if type(self.lp_balances) is not CommittedLPTableV1:
            raise TypeError("spot LP balances must be an exact committed table")
        if (
            self.balance_patch is not None
            and type(self.balance_patch) is not CanonicalBalancePatchV1
        ):
            raise TypeError("spot balance patch must be exact or None")
        if self.pool_patch is not None and type(self.pool_patch) is not CanonicalPoolPatchV1:
            raise TypeError("spot pool patch must be exact or None")
        if self.lp_patch is not None and type(self.lp_patch) is not CanonicalLPPositionPatchV1:
            raise TypeError("spot LP patch must be exact or None")
        try:
            snapshot_balance_table(self.balances)
            snapshot_pool_map(self.pools)
            snapshot_lp_table(self.lp_balances)
        except StateAdmissionError as exc:
            raise ValueError("spot candidate contains an invalid committed value") from exc


SpotTransitionResultV1: TypeAlias = SpotTransitionOkV1 | SpotTransitionRejectV1


@final
@dataclass(frozen=True, slots=True)
class SpotDeltaBatchV1:
    """One exact, bounded command value for a spot-state candidate."""

    balance_deltas: tuple[BalanceDeltaV1, ...]
    reserve_deltas: tuple[PoolReserveDeltaV1, ...]
    lp_deltas: tuple[LPPositionDeltaV1, ...]
    pool_creations: tuple[PoolCreationV1, ...]

    def __post_init__(self) -> None:
        reject = _validate_spot_delta_batch_v1(self)
        if reject is not None:
            if reject.code in {
                BalancePatchCodeV1.WRONG_EXACT_TYPE,
                LPPositionPatchCodeV1.WRONG_EXACT_TYPE,
                PoolPatchCodeV1.WRONG_EXACT_TYPE,
            }:
                raise TypeError("spot delta families must be exact tuples")
            raise ValueError(f"spot delta batch rejected: {reject.code.value}")


def _pool_reject(
    code: PoolPatchCodeV1,
    path: tuple[str | int, ...],
) -> PoolPatchRejectV1:
    return PoolPatchRejectV1(code, path)


def _validate_input_tuple_shapes(
    balance_deltas: object,
    reserve_deltas: object,
    lp_deltas: object,
    pool_creations: object,
) -> SpotTransitionRejectV1 | None:
    if type(balance_deltas) is not tuple:
        return BalancePatchRejectV1(
            code=BalancePatchCodeV1.WRONG_EXACT_TYPE,
            path=("deltas",),
        )
    if type(reserve_deltas) is not tuple:
        return _pool_reject(PoolPatchCodeV1.WRONG_EXACT_TYPE, ("reserve_deltas",))
    if type(lp_deltas) is not tuple:
        return LPPositionPatchRejectV1(
            code=LPPositionPatchCodeV1.WRONG_EXACT_TYPE,
            path=("deltas",),
        )
    if type(pool_creations) is not tuple:
        return _pool_reject(PoolPatchCodeV1.WRONG_EXACT_TYPE, ("pool_creations",))
    if (
        len(balance_deltas) + len(reserve_deltas) + len(lp_deltas) + len(pool_creations)
        > MAX_COLLECTION_ITEMS_V1
    ):
        return _pool_reject(PoolPatchCodeV1.ITEM_LIMIT, ("deltas",))
    return None


def _integer_work_bytes_v1(value: int) -> int:
    return max(1, (abs(value).bit_length() + 7) // 8)


def _spot_delta_work_bytes_v1(deltas: SpotDeltaBatchV1) -> int:
    work_bytes = 0
    for balance_delta in deltas.balance_deltas:
        work_bytes += len(balance_delta.key[0].encode("utf-8"))
        work_bytes += len(balance_delta.key[1].encode("utf-8"))
        work_bytes += _integer_work_bytes_v1(balance_delta.net_delta)
    for reserve_delta in deltas.reserve_deltas:
        work_bytes += len(reserve_delta.pool_id.encode("utf-8"))
        work_bytes += len(reserve_delta.asset.encode("utf-8"))
        work_bytes += _integer_work_bytes_v1(reserve_delta.net_delta)
    for lp_delta in deltas.lp_deltas:
        work_bytes += len(lp_delta.key[0].encode("utf-8"))
        work_bytes += len(lp_delta.key[1].encode("utf-8"))
        work_bytes += _integer_work_bytes_v1(lp_delta.net_delta)
    for creation in deltas.pool_creations:
        work_bytes += sum(
            len(value.encode("utf-8"))
            for value in (
                creation.pool_id,
                creation.asset0,
                creation.asset1,
                creation.curve_tag,
                creation.curve_params,
            )
        )
        work_bytes += _integer_work_bytes_v1(creation.fee_bps)
        work_bytes += _integer_work_bytes_v1(creation.created_at)
    return work_bytes


def _validate_spot_delta_batch_v1(
    deltas: object,
) -> SpotTransitionRejectV1 | None:
    if type(deltas) is not SpotDeltaBatchV1:
        return _pool_reject(PoolPatchCodeV1.WRONG_EXACT_TYPE, ("deltas",))
    shape_reject = _validate_input_tuple_shapes(
        deltas.balance_deltas,
        deltas.reserve_deltas,
        deltas.lp_deltas,
        deltas.pool_creations,
    )
    if shape_reject is not None:
        return shape_reject

    balance_reject = validate_balance_deltas_v1(deltas.balance_deltas)
    if balance_reject is not None:
        return balance_reject
    reserve_reject = validate_pool_deltas_v1(deltas.reserve_deltas, ())
    if reserve_reject is not None:
        return reserve_reject
    lp_reject = validate_lp_position_deltas_v1(deltas.lp_deltas)
    if lp_reject is not None:
        return lp_reject
    for index, creation in enumerate(deltas.pool_creations):
        creation_result = build_committed_pool_creation_v1(creation)
        if type(creation_result) is PoolPatchRejectV1:
            return PoolPatchRejectV1(
                creation_result.code,
                ("pool_creations", index) + creation_result.path,
            )
    if _spot_delta_work_bytes_v1(deltas) > MAX_CANONICAL_BYTES_V1:
        return _pool_reject(PoolPatchCodeV1.BYTE_LIMIT, ("deltas",))
    return None


def _insert_pool_creations_v1(
    pre: OwnedMapV1[str, CommittedPoolStateV1],
    creations: tuple[PoolCreationV1, ...],
) -> PoolPatchApplyOkV1 | PoolPatchRejectV1:
    if not creations:
        return apply_pool_deltas_v1(pre, (), ())

    writes: list[PoolWriteV1] = []
    for index, creation in enumerate(creations):
        built = build_committed_pool_creation_v1(creation)
        if type(built) is PoolPatchRejectV1:
            return PoolPatchRejectV1(built.code, ("pool_creations", index) + built.path)
        pool = built.pool
        if pre.get(pool.pool_id) is not None:
            return _pool_reject(
                PoolPatchCodeV1.EXPECTED_OLD_MISMATCH,
                ("pool_creations", index, "pool_id"),
            )
        writes.append(PoolWriteV1(pool.pool_id, None, pool))

    patch_result = build_canonical_pool_patch_v1(tuple(writes))
    if type(patch_result) is PoolPatchRejectV1:
        return patch_result
    return apply_canonical_pool_patch_v1(pre, patch_result.patch)


def _supply_deltas_from_lp_patch_v1(
    patch: CanonicalLPPositionPatchV1 | None,
) -> tuple[PoolSupplyDeltaV1, ...]:
    if patch is None:
        return ()
    supply_by_pool: dict[str, int] = {}
    for write in patch.writes:
        net = write.replacement.balance - write.expected.balance
        if net != 0:
            pool_id = write.key[1]
            supply_by_pool[pool_id] = supply_by_pool.get(pool_id, 0) + net
    return tuple(
        PoolSupplyDeltaV1(pool_id, net)
        for pool_id, net in sorted(supply_by_pool.items())
        if net != 0
    )


def _final_pool_patch_v1(
    pre: OwnedMapV1[str, CommittedPoolStateV1],
    post: OwnedMapV1[str, CommittedPoolStateV1],
) -> CanonicalPoolPatchV1 | None | PoolPatchRejectV1:
    pre_by_id = dict(pre.entries)
    post_by_id = dict(post.entries)
    writes = tuple(
        PoolWriteV1(pool_id, pre_by_id.get(pool_id), post_by_id.get(pool_id))
        for pool_id in sorted(set(pre_by_id) | set(post_by_id))
        if pre_by_id.get(pool_id) != post_by_id.get(pool_id)
    )
    if not writes:
        return None
    built = build_canonical_pool_patch_v1(writes)
    if type(built) is PoolPatchRejectV1:
        return built
    return built.patch


def apply_spot_deltas_v1(
    pre_balances: CommittedBalanceTableV1,
    pre_pools: OwnedMapV1[str, CommittedPoolStateV1],
    pre_lp_balances: CommittedLPTableV1,
    deltas: SpotDeltaBatchV1,
) -> SpotTransitionResultV1:
    """Apply all spot components as one all-or-none immutable candidate."""

    batch_reject = _validate_spot_delta_batch_v1(deltas)
    if batch_reject is not None:
        return batch_reject

    creation_result = _insert_pool_creations_v1(pre_pools, deltas.pool_creations)
    if type(creation_result) is PoolPatchRejectV1:
        return creation_result

    balance_result = apply_balance_deltas_v1(pre_balances, deltas.balance_deltas)
    if type(balance_result) is BalancePatchRejectV1:
        return balance_result
    lp_result = apply_lp_position_deltas_v1(pre_lp_balances, deltas.lp_deltas)
    if type(lp_result) is LPPositionPatchRejectV1:
        return lp_result

    for delta in deltas.lp_deltas:
        if creation_result.state.get(delta.key[1]) is None:
            return _pool_reject(
                PoolPatchCodeV1.UNKNOWN_POOL,
                ("pools", delta.key[1]),
            )

    pool_result = apply_pool_deltas_v1(
        creation_result.state,
        deltas.reserve_deltas,
        _supply_deltas_from_lp_patch_v1(lp_result.patch),
    )
    if type(pool_result) is PoolPatchRejectV1:
        return pool_result
    final_pool_patch = _final_pool_patch_v1(pre_pools, pool_result.state)
    if type(final_pool_patch) is PoolPatchRejectV1:
        return final_pool_patch

    return SpotTransitionOkV1(
        balances=balance_result.state,
        pools=pool_result.state,
        lp_balances=lp_result.state,
        balance_patch=balance_result.patch,
        pool_patch=final_pool_patch,
        lp_patch=lp_result.patch,
    )


__all__ = [
    "SpotDeltaBatchV1",
    "SpotTransitionOkV1",
    "SpotTransitionRejectV1",
    "SpotTransitionResultV1",
    "apply_spot_deltas_v1",
]
