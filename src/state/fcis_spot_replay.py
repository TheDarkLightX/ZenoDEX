"""Exact sequential spot replay over committed FCIS state values.

This module has no direct legacy-adapter imports.  It applies one bounded
net-delta batch to one immutable snapshot, returns either a typed rejection or
a complete immutable replay state, and retains every semantic pre-state cell
read before the result was known.

The LP-duration dependency consumes the same exact committed table and
revalidates it directly.  This leaf remains unmounted until the larger M5
authority switch and its differential evidence are separately reviewed.

The replay result is evidence for sequential validation.  It is deliberately
distinct from the authoritative ``FCISSpotTransitionOkV1`` candidate, which
also owns canonical patches and LP-duration policy results.
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
from .state_transitions import (
    BalanceDeltaV1,
    BalancePatchCodeV1,
    BalancePatchRejectV1,
    CanonicalBalancePatchV1,
    CanonicalLPPositionPatchV1,
    CanonicalPoolPatchV1,
    LPPositionDeltaV1,
    LPPositionPatchApplyOkV1,
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

FCISSpotReplayTransitionRejectV1: TypeAlias = (
    BalancePatchRejectV1 | LPPositionPatchRejectV1 | PoolPatchRejectV1
)


@final
@dataclass(frozen=True, slots=True)
class FCISSpotReplayReadSetV1:
    """Canonical semantic pre-state cells observed by one replay step."""

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
class FCISSpotReplayDeltaBatchV1:
    """Exact bounded net deltas for one sequential settlement replay step."""

    balance_deltas: tuple[BalanceDeltaV1, ...]
    reserve_deltas: tuple[PoolReserveDeltaV1, ...]
    lp_deltas: tuple[LPPositionDeltaV1, ...]
    pool_creations: tuple[PoolCreationV1, ...]

    def __post_init__(self) -> None:
        reject = validate_fcis_spot_replay_delta_batch_v1(self)
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
class FCISSpotReplayOkV1:
    """Complete immutable state produced by one successful replay step."""

    balances: CommittedBalanceTableV1
    pools: OwnedMapV1[str, CommittedPoolStateV1]
    lp_balances: CommittedLPTableV1

    def __post_init__(self) -> None:
        if type(self.balances) is not CommittedBalanceTableV1:
            raise TypeError("spot replay balances must be an exact committed table")
        if type(self.pools) is not OwnedMapV1:
            raise TypeError("spot replay pools must be an exact owned map")
        if type(self.lp_balances) is not CommittedLPTableV1:
            raise TypeError("spot replay LP balances must be an exact committed table")


FCISSpotReplayResultV1: TypeAlias = FCISSpotReplayOkV1 | FCISSpotReplayTransitionRejectV1


def _pool_reject(
    code: PoolPatchCodeV1,
    path: tuple[str | int, ...],
) -> PoolPatchRejectV1:
    return PoolPatchRejectV1(code, path)


def fcis_integer_work_bytes_v1(value: int) -> int:
    """Return the deterministic byte-work charge for one exact integer."""

    return max(1, (abs(value).bit_length() + 7) // 8)


def _replay_input_shape_reject_v1(
    balance_deltas: object,
    reserve_deltas: object,
    lp_deltas: object,
    pool_creations: object,
) -> FCISSpotReplayTransitionRejectV1 | None:
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


def _spot_replay_delta_work_bytes_v1(deltas: FCISSpotReplayDeltaBatchV1) -> int:
    work_bytes = 0
    for balance_delta in deltas.balance_deltas:
        work_bytes += len(balance_delta.key[0].encode("utf-8"))
        work_bytes += len(balance_delta.key[1].encode("utf-8"))
        work_bytes += fcis_integer_work_bytes_v1(balance_delta.net_delta)
    for reserve_delta in deltas.reserve_deltas:
        work_bytes += len(reserve_delta.pool_id.encode("utf-8"))
        work_bytes += len(reserve_delta.asset.encode("utf-8"))
        work_bytes += fcis_integer_work_bytes_v1(reserve_delta.net_delta)
    for lp_delta in deltas.lp_deltas:
        work_bytes += len(lp_delta.key[0].encode("utf-8"))
        work_bytes += len(lp_delta.key[1].encode("utf-8"))
        work_bytes += fcis_integer_work_bytes_v1(lp_delta.net_delta)
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
        work_bytes += fcis_integer_work_bytes_v1(creation.fee_bps)
        work_bytes += fcis_integer_work_bytes_v1(creation.created_at)
    return work_bytes


def validate_fcis_spot_replay_delta_batch_v1(
    deltas: object,
) -> FCISSpotReplayTransitionRejectV1 | None:
    """Validate one replay batch before consulting committed state."""

    if type(deltas) is not FCISSpotReplayDeltaBatchV1:
        return _pool_reject(PoolPatchCodeV1.WRONG_EXACT_TYPE, ("deltas",))
    shape_reject = _replay_input_shape_reject_v1(
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


def insert_fcis_pool_creations_observed_v1(
    pre: OwnedMapV1[str, CommittedPoolStateV1],
    creations: tuple[PoolCreationV1, ...],
) -> tuple[PoolPatchApplyOkV1 | PoolPatchRejectV1, tuple[str, ...]]:
    """Insert exact pool creations and retain every tested pool ID."""

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


def derive_fcis_pool_supply_deltas_v1(
    patch: CanonicalLPPositionPatchV1 | None,
) -> tuple[PoolSupplyDeltaV1, ...]:
    """Derive pool-supply deltas from the accepted LP patch."""

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


def unknown_fcis_lp_delta_pool_observed_v1(
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    deltas: tuple[LPPositionDeltaV1, ...],
) -> tuple[PoolPatchRejectV1 | None, tuple[str, ...]]:
    """Reject the first unknown LP pool while retaining its lookup prefix."""

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


def _compose_fcis_pool_write_v1(
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


def compose_fcis_pool_patches_v1(
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
        composed = _compose_fcis_pool_write_v1(
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


def fcis_spot_replay_read_set_v1(
    *,
    balance_keys: tuple[tuple[str, str], ...] = (),
    pool_ids: tuple[str, ...] = (),
    lp_keys: tuple[tuple[str, str], ...] = (),
) -> FCISSpotReplayReadSetV1:
    """Canonicalize already-observed semantic cell identities."""

    return FCISSpotReplayReadSetV1(
        balance_keys=tuple(sorted(set(balance_keys))),
        pool_ids=tuple(sorted(set(pool_ids))),
        lp_keys=tuple(sorted(set(lp_keys))),
    )


def apply_fcis_spot_replay_observed_v1(
    pre_balances: CommittedBalanceTableV1,
    pre_pools: OwnedMapV1[str, CommittedPoolStateV1],
    pre_lp_balances: CommittedLPTableV1,
    deltas: FCISSpotReplayDeltaBatchV1,
) -> tuple[FCISSpotReplayResultV1, FCISSpotReplayReadSetV1]:
    """Apply one exact replay step and retain every completed leaf read."""

    batch_reject = validate_fcis_spot_replay_delta_batch_v1(deltas)
    if batch_reject is not None:
        return batch_reject, FCISSpotReplayReadSetV1()

    creation_result, creation_reads = insert_fcis_pool_creations_observed_v1(
        pre_pools,
        deltas.pool_creations,
    )
    if type(creation_result) is PoolPatchRejectV1:
        return creation_result, fcis_spot_replay_read_set_v1(pool_ids=creation_reads)

    balance_result, balance_reads = apply_balance_deltas_observed_v1(
        pre_balances,
        deltas.balance_deltas,
    )
    if type(balance_result) is BalancePatchRejectV1:
        return balance_result, fcis_spot_replay_read_set_v1(
            balance_keys=balance_reads,
            pool_ids=creation_reads,
        )
    lp_result, lp_reads = apply_lp_position_deltas_observed_v1(
        pre_lp_balances,
        deltas.lp_deltas,
    )
    if type(lp_result) is LPPositionPatchRejectV1:
        return lp_result, fcis_spot_replay_read_set_v1(
            balance_keys=balance_reads,
            pool_ids=creation_reads,
            lp_keys=lp_reads,
        )

    unknown_pool_reject, existence_reads = unknown_fcis_lp_delta_pool_observed_v1(
        creation_result.state,
        deltas.lp_deltas,
    )
    if unknown_pool_reject is not None:
        return unknown_pool_reject, fcis_spot_replay_read_set_v1(
            balance_keys=balance_reads,
            pool_ids=creation_reads + existence_reads,
            lp_keys=lp_reads,
        )

    exact_lp_result = lp_result
    if type(exact_lp_result) is not LPPositionPatchApplyOkV1:
        raise RuntimeError("spot replay lost an accepted exact LP result")
    pool_result, pool_delta_reads = apply_pool_deltas_observed_v1(
        creation_result.state,
        deltas.reserve_deltas,
        derive_fcis_pool_supply_deltas_v1(exact_lp_result.patch),
    )
    if type(pool_result) is PoolPatchRejectV1:
        return pool_result, fcis_spot_replay_read_set_v1(
            balance_keys=balance_reads,
            pool_ids=creation_reads + existence_reads + pool_delta_reads,
            lp_keys=lp_reads,
        )
    final_pool_patch = compose_fcis_pool_patches_v1(
        creation_result.patch,
        pool_result.patch,
    )
    if type(final_pool_patch) is PoolPatchRejectV1:
        return final_pool_patch, fcis_spot_replay_read_set_v1(
            balance_keys=balance_reads,
            pool_ids=creation_reads + existence_reads + pool_delta_reads,
            lp_keys=lp_reads,
        )

    reads = fcis_spot_replay_read_set_v1(
        balance_keys=balance_reads,
        pool_ids=creation_reads + existence_reads + pool_delta_reads,
        lp_keys=lp_reads,
    )
    return (
        FCISSpotReplayOkV1(
            balances=balance_result.state,
            pools=pool_result.state,
            lp_balances=exact_lp_result.state,
        ),
        reads,
    )


def apply_fcis_spot_replay_v1(
    pre_balances: CommittedBalanceTableV1,
    pre_pools: OwnedMapV1[str, CommittedPoolStateV1],
    pre_lp_balances: CommittedLPTableV1,
    deltas: FCISSpotReplayDeltaBatchV1,
) -> FCISSpotReplayResultV1:
    """Apply one exact replay step and discard observational evidence."""

    result, _state_reads = apply_fcis_spot_replay_observed_v1(
        pre_balances,
        pre_pools,
        pre_lp_balances,
        deltas,
    )
    return result


FCISSpotStateReadSetV1 = FCISSpotReplayReadSetV1
FCISSpotTransitionRejectV1: TypeAlias = (
    BalancePatchRejectV1 | LPDurationTransitionRejectV1 | PoolPatchRejectV1
)


@final
@dataclass(frozen=True, slots=True)
class FCISSpotTransitionOkV1:
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

        balance_probe, _balance_reads = apply_balance_deltas_observed_v1(self.balances, ())
        pool_probe, _pool_reads = apply_pool_deltas_observed_v1(self.pools, (), ())
        lp_probe, _lp_reads = apply_lp_position_deltas_observed_v1(self.lp_balances, ())
        if (
            type(balance_probe) is BalancePatchRejectV1
            or type(pool_probe) is PoolPatchRejectV1
            or type(lp_probe) is LPPositionPatchRejectV1
        ):
            raise ValueError("spot candidate contains an invalid committed value")


FCISSpotTransitionResultV1: TypeAlias = FCISSpotTransitionOkV1 | FCISSpotTransitionRejectV1


@final
@dataclass(frozen=True, slots=True)
class FCISSpotDeltaBatchV1:
    """One exact bounded command for an authoritative spot candidate."""

    balance_deltas: tuple[BalanceDeltaV1, ...]
    reserve_deltas: tuple[PoolReserveDeltaV1, ...]
    lp_events: tuple[LPDurationEventV1, ...]
    pool_creations: tuple[PoolCreationV1, ...]

    def __post_init__(self) -> None:
        reject = validate_fcis_spot_delta_batch_v1(self)
        if reject is not None:
            if reject.code in {
                BalancePatchCodeV1.WRONG_EXACT_TYPE,
                LPDurationTransitionCodeV1.WRONG_EXACT_TYPE,
                PoolPatchCodeV1.WRONG_EXACT_TYPE,
            }:
                raise TypeError("spot delta families must be exact tuples")
            raise ValueError(f"spot delta batch rejected: {reject.code.value}")


def _authority_input_shape_reject_v1(
    balance_deltas: object,
    reserve_deltas: object,
    lp_events: object,
    pool_creations: object,
) -> FCISSpotTransitionRejectV1 | None:
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


def _spot_delta_work_bytes_v1(deltas: FCISSpotDeltaBatchV1) -> int:
    work_bytes = 0
    for balance_delta in deltas.balance_deltas:
        work_bytes += len(balance_delta.key[0].encode("utf-8"))
        work_bytes += len(balance_delta.key[1].encode("utf-8"))
        work_bytes += fcis_integer_work_bytes_v1(balance_delta.net_delta)
    for reserve_delta in deltas.reserve_deltas:
        work_bytes += len(reserve_delta.pool_id.encode("utf-8"))
        work_bytes += len(reserve_delta.asset.encode("utf-8"))
        work_bytes += fcis_integer_work_bytes_v1(reserve_delta.net_delta)
    for lp_event in deltas.lp_events:
        work_bytes += len(lp_event.key[0].encode("utf-8"))
        work_bytes += len(lp_event.key[1].encode("utf-8"))
        work_bytes += fcis_integer_work_bytes_v1(lp_event.delta_add)
        work_bytes += fcis_integer_work_bytes_v1(lp_event.delta_sub)
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
        work_bytes += fcis_integer_work_bytes_v1(creation.fee_bps)
        work_bytes += fcis_integer_work_bytes_v1(creation.created_at)
    return work_bytes


def validate_fcis_spot_delta_batch_v1(
    deltas: object,
) -> FCISSpotTransitionRejectV1 | None:
    """Validate one authoritative spot batch without reading state."""

    if type(deltas) is not FCISSpotDeltaBatchV1:
        return _pool_reject(PoolPatchCodeV1.WRONG_EXACT_TYPE, ("deltas",))
    shape_reject = _authority_input_shape_reject_v1(
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


def _unknown_fcis_lp_event_pool_observed_v1(
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


def apply_fcis_spot_deltas_observed_v1(
    pre_balances: CommittedBalanceTableV1,
    pre_pools: OwnedMapV1[str, CommittedPoolStateV1],
    pre_lp_balances: CommittedLPTableV1,
    deltas: FCISSpotDeltaBatchV1,
    *,
    now: int,
    min_age_seconds: int,
    policy: LPDurationRiskPolicyV1 | None,
) -> tuple[FCISSpotTransitionResultV1, FCISSpotStateReadSetV1]:
    """Build one all-or-none exact candidate and retain every completed read."""

    batch_reject = validate_fcis_spot_delta_batch_v1(deltas)
    if batch_reject is not None:
        return batch_reject, FCISSpotStateReadSetV1()

    lp_result, lp_reads = apply_guarded_lp_position_events_observed_v1(
        pre_lp_balances,
        deltas.lp_events,
        now=now,
        min_age_seconds=min_age_seconds,
        policy=policy,
    )
    if type(lp_result) is not LPDurationTransitionOkV1:
        return lp_result, fcis_spot_replay_read_set_v1(lp_keys=lp_reads)

    creation_result, creation_reads = insert_fcis_pool_creations_observed_v1(
        pre_pools,
        deltas.pool_creations,
    )
    if type(creation_result) is PoolPatchRejectV1:
        return creation_result, fcis_spot_replay_read_set_v1(
            pool_ids=creation_reads,
            lp_keys=lp_reads,
        )

    unknown_pool_reject, existence_reads = _unknown_fcis_lp_event_pool_observed_v1(
        creation_result.state,
        deltas.lp_events,
    )
    if unknown_pool_reject is not None:
        return unknown_pool_reject, fcis_spot_replay_read_set_v1(
            pool_ids=creation_reads + existence_reads,
            lp_keys=lp_reads,
        )

    balance_result, balance_reads = apply_balance_deltas_observed_v1(
        pre_balances,
        deltas.balance_deltas,
    )
    if type(balance_result) is BalancePatchRejectV1:
        return balance_result, fcis_spot_replay_read_set_v1(
            balance_keys=balance_reads,
            pool_ids=creation_reads + existence_reads,
            lp_keys=lp_reads,
        )

    pool_result, pool_delta_reads = apply_pool_deltas_observed_v1(
        creation_result.state,
        deltas.reserve_deltas,
        derive_fcis_pool_supply_deltas_v1(lp_result.patch),
    )
    if type(pool_result) is PoolPatchRejectV1:
        return pool_result, fcis_spot_replay_read_set_v1(
            balance_keys=balance_reads,
            pool_ids=creation_reads + existence_reads + pool_delta_reads,
            lp_keys=lp_reads,
        )
    final_pool_patch = compose_fcis_pool_patches_v1(
        creation_result.patch,
        pool_result.patch,
    )
    if type(final_pool_patch) is PoolPatchRejectV1:
        return final_pool_patch, fcis_spot_replay_read_set_v1(
            balance_keys=balance_reads,
            pool_ids=creation_reads + existence_reads + pool_delta_reads,
            lp_keys=lp_reads,
        )

    reads = fcis_spot_replay_read_set_v1(
        balance_keys=balance_reads,
        pool_ids=creation_reads + existence_reads + pool_delta_reads,
        lp_keys=lp_reads,
    )
    return (
        FCISSpotTransitionOkV1(
            balances=balance_result.state,
            pools=pool_result.state,
            lp_balances=lp_result.state,
            balance_patch=balance_result.patch,
            pool_patch=final_pool_patch,
            lp_patch=lp_result.patch,
        ),
        reads,
    )


def apply_fcis_spot_deltas_v1(
    pre_balances: CommittedBalanceTableV1,
    pre_pools: OwnedMapV1[str, CommittedPoolStateV1],
    pre_lp_balances: CommittedLPTableV1,
    deltas: FCISSpotDeltaBatchV1,
    *,
    now: int,
    min_age_seconds: int,
    policy: LPDurationRiskPolicyV1 | None,
) -> FCISSpotTransitionResultV1:
    """Build one all-or-none exact candidate and discard read evidence."""

    result, _state_reads = apply_fcis_spot_deltas_observed_v1(
        pre_balances,
        pre_pools,
        pre_lp_balances,
        deltas,
        now=now,
        min_age_seconds=min_age_seconds,
        policy=policy,
    )
    return result


__all__ = (
    "FCISSpotDeltaBatchV1",
    "FCISSpotReplayDeltaBatchV1",
    "FCISSpotReplayOkV1",
    "FCISSpotReplayReadSetV1",
    "FCISSpotReplayResultV1",
    "FCISSpotReplayTransitionRejectV1",
    "FCISSpotStateReadSetV1",
    "FCISSpotTransitionOkV1",
    "FCISSpotTransitionRejectV1",
    "FCISSpotTransitionResultV1",
    "apply_fcis_spot_deltas_observed_v1",
    "apply_fcis_spot_deltas_v1",
    "apply_fcis_spot_replay_observed_v1",
    "apply_fcis_spot_replay_v1",
    "compose_fcis_pool_patches_v1",
    "derive_fcis_pool_supply_deltas_v1",
    "fcis_integer_work_bytes_v1",
    "fcis_spot_replay_read_set_v1",
    "insert_fcis_pool_creations_observed_v1",
    "unknown_fcis_lp_delta_pool_observed_v1",
    "validate_fcis_spot_delta_batch_v1",
    "validate_fcis_spot_replay_delta_batch_v1",
)
