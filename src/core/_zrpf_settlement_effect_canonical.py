"""Canonical tuple construction for ZRPF settlement-effect plans."""

from __future__ import annotations

from typing import Callable, TypeVar

from ._zrpf_settlement_effect_common import (
    SettlementEffectPlanRejectCodeV1,
    _reject,
    _require_collection,
    _require_nonzero_hash,
)
from ._zrpf_settlement_effect_records import (
    AssetEffectV1,
    AuthorizationConsumptionV1,
    CarryEffectV1,
    LedgerCellWriteV1,
    MessageEffectV1,
    RewardEffectV1,
)

_RecordT = TypeVar(
    "_RecordT",
    LedgerCellWriteV1,
    AssetEffectV1,
    AuthorizationConsumptionV1,
    MessageEffectV1,
    CarryEffectV1,
    RewardEffectV1,
)


def _canonical_hashes(
    values: object,
    *,
    name: str,
    duplicate_code: SettlementEffectPlanRejectCodeV1,
    allow_empty: bool,
) -> tuple[str, ...]:
    rows = _require_collection(values, name=name, allow_empty=allow_empty)
    checked = tuple(
        _require_nonzero_hash(value, name=f"{name}[{index}]") for index, value in enumerate(rows)
    )
    if len(set(checked)) != len(checked):
        _reject(duplicate_code, f"{name} contains a duplicate")
    return tuple(sorted(checked))


def _canonical_records(
    values: object,
    *,
    record_type: type[_RecordT],
    key: Callable[[_RecordT], str],
    name: str,
    duplicate_code: SettlementEffectPlanRejectCodeV1,
    allow_empty: bool,
) -> tuple[_RecordT, ...]:
    rows = _require_collection(values, name=name, allow_empty=allow_empty)
    checked: list[_RecordT] = []
    keys: set[str] = set()
    for index, value in enumerate(rows):
        if type(value) is not record_type:
            _reject(
                SettlementEffectPlanRejectCodeV1.INVALID_COLLECTION,
                f"{name}[{index}] must be exactly {record_type.__name__}",
            )
        record_key = key(value)
        if record_key in keys:
            _reject(duplicate_code, f"{name} contains duplicate key {record_key}")
        keys.add(record_key)
        checked.append(value)
    return tuple(sorted(checked, key=key))


def _require_canonical_hashes(values: object, *, name: str, allow_empty: bool) -> None:
    rows = _require_collection(values, name=name, allow_empty=allow_empty)
    checked = tuple(
        _require_nonzero_hash(value, name=f"{name}[{index}]") for index, value in enumerate(rows)
    )
    if tuple(sorted(set(checked))) != checked:
        _reject(
            SettlementEffectPlanRejectCodeV1.INVALID_COLLECTION,
            f"{name} must be strictly sorted and unique",
        )


def _require_canonical_records(
    values: object,
    record_type: type[_RecordT],
    key: Callable[[_RecordT], str],
    *,
    allow_empty: bool = False,
) -> None:
    rows = _require_collection(values, name=record_type.__name__, allow_empty=allow_empty)
    checked: list[_RecordT] = []
    for index, value in enumerate(rows):
        if type(value) is not record_type:
            _reject(
                SettlementEffectPlanRejectCodeV1.INVALID_COLLECTION,
                f"{record_type.__name__}[{index}] has the wrong type",
            )
        checked.append(value)
    keys = tuple(key(value) for value in checked)
    if tuple(sorted(set(keys))) != keys:
        _reject(
            SettlementEffectPlanRejectCodeV1.INVALID_COLLECTION,
            f"{record_type.__name__} rows must be strictly sorted and unique",
        )
