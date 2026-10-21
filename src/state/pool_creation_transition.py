"""Exact creation of an empty committed pool cell."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias, final

from .owned_collections import _owned_enum_from_canonical_transition_v1
from .state_snapshot_values import (
    FCIS_STATE_SCHEMA_REVISION_V1,
    MAX_STATE_STRING_CHARACTERS_V1,
    MAX_STATE_STRING_UTF8_BYTES_V1,
    POOL_STATUS_ACTIVE_MEMBER_ORDINAL_V1,
    POOL_STATUS_ENUM_TAG_ORDINAL_V1,
    CommittedPoolStateV1,
)
from .state_transitions import PoolPatchCodeV1, PoolPatchRejectV1

PoolCreationPathV1: TypeAlias = tuple[str | int, ...]


def _reject(
    code: PoolPatchCodeV1,
    path: PoolCreationPathV1,
) -> PoolPatchRejectV1:
    return PoolPatchRejectV1(code, path)


@final
@dataclass(frozen=True, slots=True)
class PoolCreationV1:
    """Exact immutable configuration for an empty newly created pool cell."""

    pool_id: str
    asset0: str
    asset1: str
    fee_bps: int
    created_at: int
    curve_tag: str
    curve_params: str

    def __post_init__(self) -> None:
        candidate = _pool_from_creation_v1(self)
        if type(candidate) is PoolPatchRejectV1:
            if candidate.code is PoolPatchCodeV1.WRONG_EXACT_TYPE:
                raise TypeError("pool creation fields must use exact committed types")
            raise ValueError("pool creation fields violate the committed pool domain")


@final
@dataclass(frozen=True, slots=True)
class PoolCreationBuildOkV1:
    pool: CommittedPoolStateV1


PoolCreationBuildResultV1 = PoolCreationBuildOkV1 | PoolPatchRejectV1


def _string_reject(
    value: object,
    path: PoolCreationPathV1,
    *,
    minimum_characters: int,
) -> PoolPatchRejectV1 | None:
    if type(value) is not str:
        return _reject(PoolPatchCodeV1.WRONG_EXACT_TYPE, path)
    if len(value) < minimum_characters:
        return _reject(PoolPatchCodeV1.NONCANONICAL_KEY, path)
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError:
        return _reject(PoolPatchCodeV1.NONCANONICAL_KEY, path)
    if len(value) > MAX_STATE_STRING_CHARACTERS_V1 or len(encoded) > MAX_STATE_STRING_UTF8_BYTES_V1:
        return _reject(PoolPatchCodeV1.ITEM_LIMIT, path)
    return None


def _pool_from_creation_v1(
    creation: object,
) -> CommittedPoolStateV1 | PoolPatchRejectV1:
    if type(creation) is not PoolCreationV1:
        return _reject(PoolPatchCodeV1.WRONG_EXACT_TYPE, ("creation",))
    for field_name, minimum_characters in (
        ("pool_id", 1),
        ("asset0", 1),
        ("asset1", 1),
        ("curve_tag", 1),
        ("curve_params", 0),
    ):
        reject = _string_reject(
            object.__getattribute__(creation, field_name),
            ("creation", field_name),
            minimum_characters=minimum_characters,
        )
        if reject is not None:
            return reject
    if type(creation.fee_bps) is not int:
        return _reject(
            PoolPatchCodeV1.WRONG_EXACT_TYPE,
            ("creation", "fee_bps"),
        )
    if not 0 <= creation.fee_bps <= 10_000:
        return _reject(PoolPatchCodeV1.OUT_OF_RANGE, ("creation", "fee_bps"))
    if type(creation.created_at) is not int:
        return _reject(
            PoolPatchCodeV1.WRONG_EXACT_TYPE,
            ("creation", "created_at"),
        )
    if creation.created_at < 0:
        return _reject(PoolPatchCodeV1.OUT_OF_RANGE, ("creation", "created_at"))

    try:
        status = _owned_enum_from_canonical_transition_v1(
            FCIS_STATE_SCHEMA_REVISION_V1,
            POOL_STATUS_ENUM_TAG_ORDINAL_V1,
            POOL_STATUS_ACTIVE_MEMBER_ORDINAL_V1,
        )
        candidate = CommittedPoolStateV1(
            pool_id=creation.pool_id,
            asset0=creation.asset0,
            asset1=creation.asset1,
            reserve0=0,
            reserve1=0,
            fee_bps=creation.fee_bps,
            lp_supply=0,
            status=status,
            created_at=creation.created_at,
            curve_tag=creation.curve_tag,
            curve_params=creation.curve_params,
        )
    except (TypeError, ValueError):
        return _reject(PoolPatchCodeV1.INVALID_POOL_STATE, ("creation",))
    return candidate


def build_committed_pool_creation_v1(
    creation: PoolCreationV1,
) -> PoolCreationBuildResultV1:
    """Build one exact empty pool without constructing a legacy ``PoolState``."""

    candidate = _pool_from_creation_v1(creation)
    if type(candidate) is PoolPatchRejectV1:
        return candidate
    return PoolCreationBuildOkV1(candidate)


__all__ = [
    "PoolCreationBuildOkV1",
    "PoolCreationBuildResultV1",
    "PoolCreationV1",
    "build_committed_pool_creation_v1",
]
