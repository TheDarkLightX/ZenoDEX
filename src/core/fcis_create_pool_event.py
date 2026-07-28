"""Typed CREATE_POOL event expectation for exact settlement replay."""

from __future__ import annotations

from dataclasses import dataclass
from typing import final

from ..state.owned_collections import OwnedMapV1
from ..state.owned_json import (
    OWNED_JSON_OBJECT_MAP_SCHEMA_ID_V1,
    OwnedJsonObjectV1,
)
from ..state.state_snapshot_values import (
    FCIS_STATE_SCHEMA_REVISION_V1,
    POOL_STATUS_MEMBER_VALUES_V1,
    CommittedPoolStateV1,
)

_CREATE_POOL_EVENT_KEYS_V1 = (
    "asset0",
    "asset1",
    "created_at",
    "curve_params",
    "curve_tag",
    "fee_bps",
    "pool_id",
    "status",
    "type",
)


@final
@dataclass(frozen=True, slots=True)
class ExactCreatePoolEventV1:
    pool_id: str
    asset0: str
    asset1: str
    fee_bps: int
    curve_tag: str
    curve_params: str
    status: str
    created_at: int

    def __post_init__(self) -> None:
        for value in (
            self.pool_id,
            self.asset0,
            self.asset1,
            self.curve_tag,
            self.curve_params,
            self.status,
        ):
            if type(value) is not str:
                raise TypeError("CREATE_POOL event text fields must be exact")
        if type(self.fee_bps) is not int or type(self.created_at) is not int:
            raise TypeError("CREATE_POOL event integer fields must be exact")

    @property
    def entries(self) -> tuple[tuple[str, str | int], ...]:
        return (
            ("asset0", self.asset0),
            ("asset1", self.asset1),
            ("created_at", self.created_at),
            ("curve_params", self.curve_params),
            ("curve_tag", self.curve_tag),
            ("fee_bps", self.fee_bps),
            ("pool_id", self.pool_id),
            ("status", self.status),
            ("type", "CREATE_POOL"),
        )


def exact_create_pool_event_v1(pool: CommittedPoolStateV1) -> ExactCreatePoolEventV1:
    """Derive the sole protocol event projection from one exact pool."""

    if type(pool) is not CommittedPoolStateV1:
        raise TypeError("CREATE_POOL event requires an exact committed pool")
    pool.__post_init__()
    return ExactCreatePoolEventV1(
        pool_id=pool.pool_id,
        asset0=pool.asset0,
        asset1=pool.asset1,
        fee_bps=pool.fee_bps,
        curve_tag=pool.curve_tag,
        curve_params=pool.curve_params,
        status=POOL_STATUS_MEMBER_VALUES_V1[pool.status.member_ordinal],
        created_at=pool.created_at,
    )


def create_pool_event_matches_owned_v1(
    expected: ExactCreatePoolEventV1,
    supplied: OwnedJsonObjectV1,
) -> bool:
    """Compare exact protocol entries without projecting a mutable dictionary."""

    if type(expected) is not ExactCreatePoolEventV1:
        raise TypeError("expected CREATE_POOL event must be exact")
    expected.__post_init__()
    if type(supplied) is not OwnedMapV1:
        return False
    if (
        supplied.schema_revision != FCIS_STATE_SCHEMA_REVISION_V1
        or supplied.schema_id != OWNED_JSON_OBJECT_MAP_SCHEMA_ID_V1
    ):
        return False
    entries = supplied.entries
    if tuple(key for key, _value in entries) != _CREATE_POOL_EVENT_KEYS_V1:
        return False
    return entries == expected.entries


__all__ = (
    "ExactCreatePoolEventV1",
    "create_pool_event_matches_owned_v1",
    "exact_create_pool_event_v1",
)
