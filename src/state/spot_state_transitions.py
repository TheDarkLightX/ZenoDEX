"""Atomic exact spot-state transitions over committed FCIS values.

This module composes balance, pool, and LP leaf patches into one all-or-none
candidate. The public aggregate consumes full LP lifecycle events, so its
accepted candidate includes balance, duration metadata, and the age preflight
from one guarded LP result. Pool LP-supply deltas derive from that result;
callers cannot provide a contradictory supply change.

Strong settlement replay uses a private balance-only helper while validating
sequential kernel behavior. That helper cannot construct the public
``SpotTransitionOkV1`` authority value.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias, final

from .lp_duration_transitions import (
    LPDurationEventV1,
    LPDurationRiskPolicyV1,
    LPDurationTransitionCodeV1,
    LPDurationTransitionOkV1,
    LPDurationTransitionRejectV1,
    apply_guarded_lp_position_events_observed_v1,
    validate_lp_duration_events_v1,
)
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
    apply_balance_deltas_observed_v1,
    apply_canonical_pool_patch_v1,
    apply_lp_position_deltas_observed_v1,
    apply_pool_deltas_observed_v1,
    apply_pool_deltas_v1,
    build_canonical_pool_patch_v1,
    validate_balance_deltas_v1,
    validate_lp_position_deltas_v1,
    validate_pool_deltas_v1,
)

SpotTransitionRejectV1: TypeAlias = (
    BalancePatchRejectV1 | LPDurationTransitionRejectV1 | PoolPatchRejectV1
)
_SpotReplayTransitionRejectV1: TypeAlias = (
    BalancePatchRejectV1 | LPPositionPatchRejectV1 | PoolPatchRejectV1
)


@final
@dataclass(frozen=True, slots=True)
class SpotStateReadSetV1:
    """Canonical semantic pre-state cells observed by one accepted spot step."""

    balance_keys: tuple[tuple[str, str], ...] = ()
    pool_ids: tuple[str, ...] = ()
    lp_keys: tuple[tuple[str, str], ...] = ()

    def __post_init__(self) -> None:
        if self.balance_keys != tuple(sorted(set(self.balance_keys))):
            raise ValueError("spot balance read keys must be canonical")
        if self.pool_ids != tuple(sorted(set(self.pool_ids))):
            raise ValueError("spot pool read IDs must be canonical")
        if self.lp_keys != tuple(sorted(set(self.lp_keys))):
            raise ValueError("spot LP read keys must be canonical")
        if any(
            type(key) is not tuple
            or len(key) != 2
            or type(key[0]) is not str
            or type(key[1]) is not str
            for key in self.balance_keys + self.lp_keys
        ):
            raise TypeError("spot pair read keys must be exact string pairs")
        if any(type(pool_id) is not str for pool_id in self.pool_ids):
            raise TypeError("spot pool read IDs must be exact strings")


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
    """One exact, bounded command value for an authoritative spot candidate."""

    balance_deltas: tuple[BalanceDeltaV1, ...]
    reserve_deltas: tuple[PoolReserveDeltaV1, ...]
    lp_events: tuple[LPDurationEventV1, ...]
    pool_creations: tuple[PoolCreationV1, ...]

    def __post_init__(self) -> None:
        reject = _validate_spot_delta_batch_v1(self)
        if reject is not None:
            if reject.code in {
                BalancePatchCodeV1.WRONG_EXACT_TYPE,
                LPDurationTransitionCodeV1.WRONG_EXACT_TYPE,
                PoolPatchCodeV1.WRONG_EXACT_TYPE,
            }:
                raise TypeError("spot delta families must be exact tuples")
            raise ValueError(f"spot delta batch rejected: {reject.code.value}")


@final
@dataclass(frozen=True, slots=True)
class _SpotReplayDeltaBatchV1:
    """Private net-only replay command; never an authoritative candidate."""

    balance_deltas: tuple[BalanceDeltaV1, ...]
    reserve_deltas: tuple[PoolReserveDeltaV1, ...]
    lp_deltas: tuple[LPPositionDeltaV1, ...]
    pool_creations: tuple[PoolCreationV1, ...]

    def __post_init__(self) -> None:
        reject = _validate_spot_replay_delta_batch_v1(self)
        if reject is not None:
            if reject.code in {
                BalancePatchCodeV1.WRONG_EXACT_TYPE,
                LPPositionPatchCodeV1.WRONG_EXACT_TYPE,
                PoolPatchCodeV1.WRONG_EXACT_TYPE,
            }:
                raise TypeError("spot replay delta families must be exact tuples")
            raise ValueError(f"spot replay delta batch rejected: {reject.code.value}")


@final
@dataclass(frozen=True, slots=True)
class _SpotReplayOkV1:
    """Internal sequential-replay state with no authority-candidate type."""

    balances: CommittedBalanceTableV1
    pools: OwnedMapV1[str, CommittedPoolStateV1]
    lp_balances: CommittedLPTableV1


_SpotReplayResultV1: TypeAlias = _SpotReplayOkV1 | _SpotReplayTransitionRejectV1


def _pool_reject(
    code: PoolPatchCodeV1,
    path: tuple[str | int, ...],
) -> PoolPatchRejectV1:
    return PoolPatchRejectV1(code, path)


def _validate_authority_input_tuple_shapes(
    balance_deltas: object,
    reserve_deltas: object,
    lp_events: object,
    pool_creations: object,
) -> SpotTransitionRejectV1 | None:
    if type(balance_deltas) is not tuple:
        return BalancePatchRejectV1(
            code=BalancePatchCodeV1.WRONG_EXACT_TYPE,
            path=("deltas",),
        )
    if type(reserve_deltas) is not tuple:
        return _pool_reject(PoolPatchCodeV1.WRONG_EXACT_TYPE, ("reserve_deltas",))
    if type(lp_events) is not tuple:
        return LPDurationTransitionRejectV1(
            code=LPDurationTransitionCodeV1.WRONG_EXACT_TYPE,
            path=("events",),
        )
    if type(pool_creations) is not tuple:
        return _pool_reject(PoolPatchCodeV1.WRONG_EXACT_TYPE, ("pool_creations",))
    if (
        len(balance_deltas) + len(reserve_deltas) + len(lp_events) + len(pool_creations)
        > MAX_COLLECTION_ITEMS_V1
    ):
        return _pool_reject(PoolPatchCodeV1.ITEM_LIMIT, ("deltas",))
    return None


def _validate_replay_input_tuple_shapes(
    balance_deltas: object,
    reserve_deltas: object,
    lp_deltas: object,
    pool_creations: object,
) -> _SpotReplayTransitionRejectV1 | None:
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
    for lp_event in deltas.lp_events:
        work_bytes += len(lp_event.key[0].encode("utf-8"))
        work_bytes += len(lp_event.key[1].encode("utf-8"))
        work_bytes += _integer_work_bytes_v1(lp_event.delta_add)
        work_bytes += _integer_work_bytes_v1(lp_event.delta_sub)
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


def _spot_replay_delta_work_bytes_v1(deltas: _SpotReplayDeltaBatchV1) -> int:
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
    shape_reject = _validate_authority_input_tuple_shapes(
        deltas.balance_deltas,
        deltas.reserve_deltas,
        deltas.lp_events,
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
    lp_reject = validate_lp_duration_events_v1(deltas.lp_events)
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


def _validate_spot_replay_delta_batch_v1(
    deltas: object,
) -> _SpotReplayTransitionRejectV1 | None:
    if type(deltas) is not _SpotReplayDeltaBatchV1:
        return _pool_reject(PoolPatchCodeV1.WRONG_EXACT_TYPE, ("deltas",))
    shape_reject = _validate_replay_input_tuple_shapes(
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
    if _spot_replay_delta_work_bytes_v1(deltas) > MAX_CANONICAL_BYTES_V1:
        return _pool_reject(PoolPatchCodeV1.BYTE_LIMIT, ("deltas",))
    return None


def _insert_pool_creations_observed_v1(
    pre: OwnedMapV1[str, CommittedPoolStateV1],
    creations: tuple[PoolCreationV1, ...],
) -> tuple[PoolPatchApplyOkV1 | PoolPatchRejectV1, tuple[str, ...]]:
    if not creations:
        return apply_pool_deltas_v1(pre, (), ()), ()

    writes: list[PoolWriteV1] = []
    observed_pool_ids: list[str] = []
    for index, creation in enumerate(creations):
        built = build_committed_pool_creation_v1(creation)
        if type(built) is PoolPatchRejectV1:
            return (
                PoolPatchRejectV1(built.code, ("pool_creations", index) + built.path),
                tuple(observed_pool_ids),
            )
        pool = built.pool
        observed_pool_ids.append(pool.pool_id)
        if pre.get(pool.pool_id) is not None:
            return (
                _pool_reject(
                    PoolPatchCodeV1.EXPECTED_OLD_MISMATCH,
                    ("pool_creations", index, "pool_id"),
                ),
                tuple(observed_pool_ids),
            )
        writes.append(PoolWriteV1(pool.pool_id, None, pool))

    patch_result = build_canonical_pool_patch_v1(tuple(writes))
    if type(patch_result) is PoolPatchRejectV1:
        return patch_result, tuple(observed_pool_ids)
    return (
        apply_canonical_pool_patch_v1(pre, patch_result.patch),
        tuple(observed_pool_ids),
    )


def _insert_pool_creations_v1(
    pre: OwnedMapV1[str, CommittedPoolStateV1],
    creations: tuple[PoolCreationV1, ...],
) -> PoolPatchApplyOkV1 | PoolPatchRejectV1:
    result, _observed_pool_ids = _insert_pool_creations_observed_v1(pre, creations)
    return result


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


def _unknown_lp_event_pool_reject_observed_v1(
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    events: tuple[LPDurationEventV1, ...],
) -> tuple[PoolPatchRejectV1 | None, tuple[str, ...]]:
    observed_pool_ids: list[str] = []
    for event in events:
        pool_id = event.key[1]
        observed_pool_ids.append(pool_id)
        if pools.get(pool_id) is None:
            return (
                _pool_reject(
                    PoolPatchCodeV1.UNKNOWN_POOL,
                    ("pools", pool_id),
                ),
                tuple(sorted(set(observed_pool_ids))),
            )
    return None, tuple(sorted(set(observed_pool_ids)))


def _unknown_lp_event_pool_reject_v1(
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    events: tuple[LPDurationEventV1, ...],
) -> PoolPatchRejectV1 | None:
    reject, _observed_pool_ids = _unknown_lp_event_pool_reject_observed_v1(pools, events)
    return reject


def _unknown_lp_delta_pool_reject_observed_v1(
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    deltas: tuple[LPPositionDeltaV1, ...],
) -> tuple[PoolPatchRejectV1 | None, tuple[str, ...]]:
    observed_pool_ids: list[str] = []
    for delta in deltas:
        pool_id = delta.key[1]
        observed_pool_ids.append(pool_id)
        if pools.get(pool_id) is None:
            return (
                _pool_reject(
                    PoolPatchCodeV1.UNKNOWN_POOL,
                    ("pools", pool_id),
                ),
                tuple(sorted(set(observed_pool_ids))),
            )
    return None, tuple(sorted(set(observed_pool_ids)))


def _compose_pool_write_v1(
    pool_id: str,
    first: PoolWriteV1 | None,
    second: PoolWriteV1 | None,
) -> PoolWriteV1 | None | PoolPatchRejectV1:
    if first is None:
        if second is None:
            raise RuntimeError("pool patch composition lost a touched key")
        return second
    if second is None:
        return first
    if first.replacement != second.expected:
        return _pool_reject(
            PoolPatchCodeV1.EXPECTED_OLD_MISMATCH,
            ("writes", pool_id, "expected"),
        )
    if first.expected == second.replacement:
        return None
    return PoolWriteV1(pool_id, first.expected, second.replacement)


def _compose_pool_patches_v1(
    first: CanonicalPoolPatchV1 | None,
    second: CanonicalPoolPatchV1 | None,
) -> CanonicalPoolPatchV1 | None | PoolPatchRejectV1:
    """Compose two already-applied patches without scanning untouched pools."""

    first_writes = () if first is None else first.writes
    second_writes = () if second is None else second.writes
    first_by_id = {write.pool_id: write for write in first_writes}
    second_by_id = {write.pool_id: write for write in second_writes}
    writes: list[PoolWriteV1] = []
    for pool_id in sorted(set(first_by_id) | set(second_by_id)):
        composed = _compose_pool_write_v1(
            pool_id,
            first_by_id.get(pool_id),
            second_by_id.get(pool_id),
        )
        if type(composed) is PoolPatchRejectV1:
            return composed
        if composed is not None:
            writes.append(composed)
    if not writes:
        return None
    built = build_canonical_pool_patch_v1(tuple(writes))
    if type(built) is PoolPatchRejectV1:
        return built
    return built.patch


def _apply_spot_replay_deltas_observed_v1(
    pre_balances: CommittedBalanceTableV1,
    pre_pools: OwnedMapV1[str, CommittedPoolStateV1],
    pre_lp_balances: CommittedLPTableV1,
    deltas: _SpotReplayDeltaBatchV1,
) -> tuple[_SpotReplayResultV1, SpotStateReadSetV1]:
    """Apply one private replay step and retain every completed leaf read."""

    batch_reject = _validate_spot_replay_delta_batch_v1(deltas)
    if batch_reject is not None:
        return batch_reject, SpotStateReadSetV1()

    creation_result, creation_reads = _insert_pool_creations_observed_v1(
        pre_pools,
        deltas.pool_creations,
    )
    if type(creation_result) is PoolPatchRejectV1:
        return creation_result, _spot_state_reads_v1(pool_ids=creation_reads)

    balance_result, balance_reads = apply_balance_deltas_observed_v1(
        pre_balances,
        deltas.balance_deltas,
    )
    if type(balance_result) is BalancePatchRejectV1:
        return balance_result, _spot_state_reads_v1(
            balance_keys=balance_reads,
            pool_ids=creation_reads,
        )
    lp_result, lp_reads = apply_lp_position_deltas_observed_v1(
        pre_lp_balances,
        deltas.lp_deltas,
    )
    if type(lp_result) is LPPositionPatchRejectV1:
        return lp_result, _spot_state_reads_v1(
            balance_keys=balance_reads,
            pool_ids=creation_reads,
            lp_keys=lp_reads,
        )

    unknown_pool_reject, existence_reads = _unknown_lp_delta_pool_reject_observed_v1(
        creation_result.state,
        deltas.lp_deltas,
    )
    if unknown_pool_reject is not None:
        return unknown_pool_reject, _spot_state_reads_v1(
            balance_keys=balance_reads,
            pool_ids=creation_reads + existence_reads,
            lp_keys=lp_reads,
        )

    pool_result, pool_delta_reads = apply_pool_deltas_observed_v1(
        creation_result.state,
        deltas.reserve_deltas,
        _supply_deltas_from_lp_patch_v1(lp_result.patch),
    )
    if type(pool_result) is PoolPatchRejectV1:
        return pool_result, _spot_state_reads_v1(
            balance_keys=balance_reads,
            pool_ids=creation_reads + existence_reads + pool_delta_reads,
            lp_keys=lp_reads,
        )
    final_pool_patch = _compose_pool_patches_v1(
        creation_result.patch,
        pool_result.patch,
    )
    if type(final_pool_patch) is PoolPatchRejectV1:
        return final_pool_patch, _spot_state_reads_v1(
            balance_keys=balance_reads,
            pool_ids=creation_reads + existence_reads + pool_delta_reads,
            lp_keys=lp_reads,
        )

    reads = _spot_state_reads_v1(
        balance_keys=balance_reads,
        pool_ids=creation_reads + existence_reads + pool_delta_reads,
        lp_keys=lp_reads,
    )
    return (
        _SpotReplayOkV1(
            balances=balance_result.state,
            pools=pool_result.state,
            lp_balances=lp_result.state,
        ),
        reads,
    )


def _apply_spot_replay_deltas_v1(
    pre_balances: CommittedBalanceTableV1,
    pre_pools: OwnedMapV1[str, CommittedPoolStateV1],
    pre_lp_balances: CommittedLPTableV1,
    deltas: _SpotReplayDeltaBatchV1,
) -> _SpotReplayResultV1:
    """Apply private replay deltas and discard non-authoritative read evidence."""

    result, _state_reads = _apply_spot_replay_deltas_observed_v1(
        pre_balances,
        pre_pools,
        pre_lp_balances,
        deltas,
    )
    return result


def _spot_state_reads_v1(
    *,
    balance_keys: tuple[tuple[str, str], ...] = (),
    pool_ids: tuple[str, ...] = (),
    lp_keys: tuple[tuple[str, str], ...] = (),
) -> SpotStateReadSetV1:
    return SpotStateReadSetV1(
        balance_keys=tuple(sorted(set(balance_keys))),
        pool_ids=tuple(sorted(set(pool_ids))),
        lp_keys=tuple(sorted(set(lp_keys))),
    )


def apply_spot_deltas_observed_v1(
    pre_balances: CommittedBalanceTableV1,
    pre_pools: OwnedMapV1[str, CommittedPoolStateV1],
    pre_lp_balances: CommittedLPTableV1,
    deltas: SpotDeltaBatchV1,
    *,
    now: int,
    min_age_seconds: int,
    policy: LPDurationRiskPolicyV1 | None,
) -> tuple[SpotTransitionResultV1, SpotStateReadSetV1]:
    """Build one all-or-none candidate and retain reads on every result path."""

    batch_reject = _validate_spot_delta_batch_v1(deltas)
    if batch_reject is not None:
        return batch_reject, SpotStateReadSetV1()

    lp_result, lp_reads = apply_guarded_lp_position_events_observed_v1(
        pre_lp_balances,
        deltas.lp_events,
        now=now,
        min_age_seconds=min_age_seconds,
        policy=policy,
    )
    if type(lp_result) is not LPDurationTransitionOkV1:
        return lp_result, _spot_state_reads_v1(lp_keys=lp_reads)

    creation_result, creation_reads = _insert_pool_creations_observed_v1(
        pre_pools,
        deltas.pool_creations,
    )
    if type(creation_result) is PoolPatchRejectV1:
        return creation_result, _spot_state_reads_v1(
            pool_ids=creation_reads,
            lp_keys=lp_reads,
        )

    unknown_pool_reject, existence_reads = _unknown_lp_event_pool_reject_observed_v1(
        creation_result.state,
        deltas.lp_events,
    )
    if unknown_pool_reject is not None:
        return unknown_pool_reject, _spot_state_reads_v1(
            pool_ids=creation_reads + existence_reads,
            lp_keys=lp_reads,
        )

    balance_result, balance_reads = apply_balance_deltas_observed_v1(
        pre_balances,
        deltas.balance_deltas,
    )
    if type(balance_result) is BalancePatchRejectV1:
        return balance_result, _spot_state_reads_v1(
            balance_keys=balance_reads,
            pool_ids=creation_reads + existence_reads,
            lp_keys=lp_reads,
        )

    pool_result, pool_delta_reads = apply_pool_deltas_observed_v1(
        creation_result.state,
        deltas.reserve_deltas,
        _supply_deltas_from_lp_patch_v1(lp_result.patch),
    )
    if type(pool_result) is PoolPatchRejectV1:
        return pool_result, _spot_state_reads_v1(
            balance_keys=balance_reads,
            pool_ids=creation_reads + existence_reads + pool_delta_reads,
            lp_keys=lp_reads,
        )
    final_pool_patch = _compose_pool_patches_v1(
        creation_result.patch,
        pool_result.patch,
    )
    if type(final_pool_patch) is PoolPatchRejectV1:
        return final_pool_patch, _spot_state_reads_v1(
            balance_keys=balance_reads,
            pool_ids=creation_reads + existence_reads + pool_delta_reads,
            lp_keys=lp_reads,
        )

    reads = _spot_state_reads_v1(
        balance_keys=balance_reads,
        pool_ids=creation_reads + existence_reads + pool_delta_reads,
        lp_keys=lp_reads,
    )
    return (
        SpotTransitionOkV1(
            balances=balance_result.state,
            pools=pool_result.state,
            lp_balances=lp_result.state,
            balance_patch=balance_result.patch,
            pool_patch=final_pool_patch,
            lp_patch=lp_result.patch,
        ),
        reads,
    )


def apply_spot_deltas_v1(
    pre_balances: CommittedBalanceTableV1,
    pre_pools: OwnedMapV1[str, CommittedPoolStateV1],
    pre_lp_balances: CommittedLPTableV1,
    deltas: SpotDeltaBatchV1,
    *,
    now: int,
    min_age_seconds: int,
    policy: LPDurationRiskPolicyV1 | None,
) -> SpotTransitionResultV1:
    """Build one all-or-none candidate and discard observational evidence."""

    result, _state_reads = apply_spot_deltas_observed_v1(
        pre_balances,
        pre_pools,
        pre_lp_balances,
        deltas,
        now=now,
        min_age_seconds=min_age_seconds,
        policy=policy,
    )
    return result


__all__ = [
    "SpotDeltaBatchV1",
    "SpotStateReadSetV1",
    "SpotTransitionOkV1",
    "SpotTransitionRejectV1",
    "SpotTransitionResultV1",
    "apply_spot_deltas_observed_v1",
    "apply_spot_deltas_v1",
]
