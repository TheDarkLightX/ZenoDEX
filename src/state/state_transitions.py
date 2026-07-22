"""Pure return-new transitions over exact FCIS committed state values.

This first slice defines the logical balance-patch relation. It deliberately
does not expose a mutable projection, depend on a collection library's tree
shape, emit effects, or commit storage. Those are separate contracts.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from types import MappingProxyType
from typing import TypeAlias, cast, final

from .owned_collections import (
    OwnedMapV1,
    _owned_map_from_canonical_transition_v1,
)
from .snapshot_combinators import MAX_CANONICAL_BYTES_V1
from .state_snapshot_values import (
    BALANCE_MAP_SCHEMA_ID_V1,
    FCIS_STATE_SCHEMA_REVISION_V1,
    MAX_BALANCES_V1,
    MAX_STATE_STRING_CHARACTERS_V1,
    MAX_STATE_STRING_UTF8_BYTES_V1,
    BalanceKeyV1,
    CommittedBalanceTableV1,
)

BalancePatchPathPartV1: TypeAlias = str | int
BalancePatchPathV1: TypeAlias = tuple[BalancePatchPathPartV1, ...]
_MAPPING_PROXY_TYPE: type[object] = type(MappingProxyType({}))


class BalancePatchCodeV1(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    ITEM_LIMIT = "item_limit"
    BYTE_LIMIT = "byte_limit"
    NONCANONICAL_KEY = "noncanonical_key"
    OUT_OF_RANGE = "out_of_range"
    EMPTY_PATCH = "empty_patch"
    DUPLICATE_WRITE = "duplicate_write"
    NO_OP_WRITE = "no_op_write"
    NONCANONICAL_PATCH = "noncanonical_patch"
    EXPECTED_OLD_MISMATCH = "expected_old_mismatch"
    INVALID_PRESTATE = "invalid_prestate"


@final
@dataclass(frozen=True, slots=True)
class BalancePatchRejectV1:
    """Typed no-output rejection for patch construction or application."""

    code: BalancePatchCodeV1
    path: BalancePatchPathV1


def _reject(
    code: BalancePatchCodeV1,
    path: BalancePatchPathV1,
) -> BalancePatchRejectV1:
    return BalancePatchRejectV1(code, path)


def _balance_key_reject(
    key: object,
    path: BalancePatchPathV1,
) -> BalancePatchRejectV1 | None:
    if type(key) is not tuple or len(key) != 2:
        return _reject(BalancePatchCodeV1.WRONG_EXACT_TYPE, path)
    for index, component in enumerate(key):
        component_path = path + (index,)
        if type(component) is not str:
            return _reject(BalancePatchCodeV1.WRONG_EXACT_TYPE, component_path)
        if not component:
            return _reject(BalancePatchCodeV1.NONCANONICAL_KEY, component_path)
        if len(component) > MAX_STATE_STRING_CHARACTERS_V1:
            return _reject(BalancePatchCodeV1.ITEM_LIMIT, component_path)
        try:
            encoded = component.encode("utf-8")
        except UnicodeEncodeError:
            return _reject(BalancePatchCodeV1.NONCANONICAL_KEY, component_path)
        if len(encoded) > MAX_STATE_STRING_UTF8_BYTES_V1:
            return _reject(BalancePatchCodeV1.ITEM_LIMIT, component_path)
    return None


def _write_representation_reject(
    write: object,
    path: BalancePatchPathV1,
) -> BalancePatchRejectV1 | None:
    if type(write) is not BalanceWriteV1:
        return _reject(BalancePatchCodeV1.WRONG_EXACT_TYPE, path)
    key_reject = _balance_key_reject(write.key, path + ("key",))
    if key_reject is not None:
        return key_reject
    if type(write.expected_old) is not int:
        return _reject(BalancePatchCodeV1.WRONG_EXACT_TYPE, path + ("expected_old",))
    if write.expected_old < 0:
        return _reject(BalancePatchCodeV1.OUT_OF_RANGE, path + ("expected_old",))
    if write.replacement is not None:
        if type(write.replacement) is not int:
            return _reject(BalancePatchCodeV1.WRONG_EXACT_TYPE, path + ("replacement",))
        if write.replacement <= 0:
            return _reject(BalancePatchCodeV1.OUT_OF_RANGE, path + ("replacement",))
    return None


@final
@dataclass(frozen=True, slots=True)
class BalanceWriteV1:
    """One exact compare-and-replace operation for a logical balance cell."""

    key: BalanceKeyV1
    expected_old: int
    replacement: int | None

    def __post_init__(self) -> None:
        key_reject = _balance_key_reject(self.key, ("key",))
        if key_reject is not None:
            if key_reject.code is BalancePatchCodeV1.WRONG_EXACT_TYPE:
                raise TypeError("balance key must be an exact pair of strings")
            if key_reject.code is BalancePatchCodeV1.ITEM_LIMIT:
                raise ValueError("balance key exceeds its mounted limit")
            key_component = self.key[key_reject.path[-1]]
            if key_component == "":
                raise ValueError("balance key components must be nonempty")
            raise ValueError("balance key must contain Unicode scalar strings")
        if type(self.expected_old) is not int or self.expected_old < 0:
            raise TypeError("expected_old must be an exact nonnegative integer")
        if self.replacement is not None and (
            type(self.replacement) is not int or self.replacement <= 0
        ):
            raise TypeError("replacement must be an exact positive integer or None")


@final
@dataclass(frozen=True, slots=True)
class BalanceDeltaV1:
    """One exact additive balance atom for deterministic reduction."""

    key: BalanceKeyV1
    net_delta: int

    def __post_init__(self) -> None:
        key_reject = _balance_key_reject(self.key, ("key",))
        if key_reject is not None:
            if key_reject.code is BalancePatchCodeV1.WRONG_EXACT_TYPE:
                raise TypeError("balance delta key must be an exact pair of strings")
            raise ValueError("balance delta key is not canonical")
        if type(self.net_delta) is not int:
            raise TypeError("balance net_delta must be an exact integer")
        if self.net_delta == 0:
            raise ValueError("balance net_delta must be nonzero")


def _write_is_noop(write: BalanceWriteV1) -> bool:
    replacement = 0 if write.replacement is None else write.replacement
    return write.expected_old == replacement


def _canonical_writes_reject(
    writes: object,
    *,
    invalid_code: BalancePatchCodeV1,
) -> BalancePatchRejectV1 | None:
    if type(writes) is not tuple:
        return _reject(invalid_code, ("writes",))
    if not writes:
        return _reject(invalid_code, ("writes",))
    if len(writes) > MAX_BALANCES_V1:
        return _reject(BalancePatchCodeV1.ITEM_LIMIT, ("writes",))

    previous_key: BalanceKeyV1 | None = None
    for index, write in enumerate(writes):
        path: BalancePatchPathV1 = ("writes", index)
        representation_reject = _write_representation_reject(write, path)
        if representation_reject is not None:
            return _reject(invalid_code, representation_reject.path)
        exact_write = cast(BalanceWriteV1, write)
        if _write_is_noop(exact_write):
            return _reject(invalid_code, path)
        if previous_key is not None and previous_key >= exact_write.key:
            return _reject(invalid_code, path + ("key",))
        previous_key = exact_write.key
    return None


@final
@dataclass(frozen=True, slots=True)
class CanonicalBalancePatchV1:
    """Nonempty, sorted, duplicate-free balance compare-and-replace patch."""

    writes: tuple[BalanceWriteV1, ...]

    def __post_init__(self) -> None:
        reject = _canonical_writes_reject(
            self.writes,
            invalid_code=BalancePatchCodeV1.NONCANONICAL_PATCH,
        )
        if reject is not None:
            raise ValueError("CanonicalBalancePatchV1 requires canonical writes")


@final
@dataclass(frozen=True, slots=True)
class BalancePatchBuildOkV1:
    patch: CanonicalBalancePatchV1


@final
@dataclass(frozen=True, slots=True)
class BalancePatchApplyOkV1:
    state: CommittedBalanceTableV1


BalancePatchBuildResultV1 = BalancePatchBuildOkV1 | BalancePatchRejectV1
BalancePatchApplyResultV1 = BalancePatchApplyOkV1 | BalancePatchRejectV1


def _delta_representation_reject(delta: object) -> BalancePatchRejectV1 | None:
    if type(delta) is not BalanceDeltaV1:
        return _reject(BalancePatchCodeV1.WRONG_EXACT_TYPE, ("deltas",))
    key_reject = _balance_key_reject(delta.key, ("deltas", "key"))
    if key_reject is not None:
        return key_reject
    if type(delta.net_delta) is not int:
        return _reject(BalancePatchCodeV1.WRONG_EXACT_TYPE, ("deltas", "net_delta"))
    if delta.net_delta == 0:
        return _reject(BalancePatchCodeV1.NO_OP_WRITE, ("deltas", "net_delta"))
    return None


def _rejection_order_key(reject: BalancePatchRejectV1) -> tuple[str, tuple[tuple[str, str], ...]]:
    return (
        reject.code.value,
        tuple((type(part).__name__, str(part)) for part in reject.path),
    )


def apply_balance_deltas_v1(
    pre: CommittedBalanceTableV1,
    deltas: tuple[BalanceDeltaV1, ...],
) -> BalancePatchApplyResultV1:
    """Reduce additive atoms canonically and apply one compare-and-replace patch.

    Delta order has no semantic effect. Python integers make the additive
    reduction exact; no regrouping-dependent overflow or rounding exists.
    Cancellation to an empty patch returns the validated immutable pre-state.
    """

    pre_entries = _validated_balance_entries_v1(pre)
    if type(pre_entries) is BalancePatchRejectV1:
        return pre_entries
    if type(deltas) is not tuple:
        return _reject(BalancePatchCodeV1.WRONG_EXACT_TYPE, ("deltas",))
    if len(deltas) > MAX_BALANCES_V1:
        return _reject(BalancePatchCodeV1.ITEM_LIMIT, ("deltas",))

    representation_rejects = tuple(
        reject
        for delta in deltas
        if (reject := _delta_representation_reject(delta)) is not None
    )
    if representation_rejects:
        return min(representation_rejects, key=_rejection_order_key)

    work_bytes = 0
    for delta in deltas:
        work_bytes += len(delta.key[0].encode("utf-8"))
        work_bytes += len(delta.key[1].encode("utf-8"))
        work_bytes += max(1, (abs(delta.net_delta).bit_length() + 7) // 8)
        if work_bytes > MAX_CANONICAL_BYTES_V1:
            return _reject(BalancePatchCodeV1.BYTE_LIMIT, ("deltas",))

    aggregate: dict[BalanceKeyV1, int] = {}
    for delta in deltas:
        aggregate[delta.key] = aggregate.get(delta.key, 0) + delta.net_delta

    current_by_key = dict(pre_entries)
    writes: list[BalanceWriteV1] = []
    for key, net_delta in sorted(aggregate.items(), key=lambda item: item[0]):
        if net_delta == 0:
            continue
        current = current_by_key.get(key, 0)
        replacement = current + net_delta
        if replacement < 0:
            return _reject(BalancePatchCodeV1.OUT_OF_RANGE, ("deltas", "net_delta"))
        writes.append(
            BalanceWriteV1(
                key=key,
                expected_old=current,
                replacement=None if replacement == 0 else replacement,
            )
        )

    if not writes:
        return BalancePatchApplyOkV1(pre)
    patch_result = build_canonical_balance_patch_v1(tuple(writes))
    if type(patch_result) is BalancePatchRejectV1:
        return patch_result
    return apply_canonical_balance_patch_v1(pre, patch_result.patch)


def build_canonical_balance_patch_v1(
    writes: tuple[BalanceWriteV1, ...],
) -> BalancePatchBuildResultV1:
    """Normalize exact writes into one canonical patch or a typed rejection.

    Input tuple order has no semantic effect after each exact write has passed
    representation checks. Duplicate logical cells and semantic no-ops reject.
    """

    if type(writes) is not tuple:
        return _reject(BalancePatchCodeV1.WRONG_EXACT_TYPE, ("writes",))
    if not writes:
        return _reject(BalancePatchCodeV1.EMPTY_PATCH, ("writes",))
    if len(writes) > MAX_BALANCES_V1:
        return _reject(BalancePatchCodeV1.ITEM_LIMIT, ("writes",))

    for index, write in enumerate(writes):
        path: BalancePatchPathV1 = ("writes", index)
        representation_reject = _write_representation_reject(write, path)
        if representation_reject is not None:
            return representation_reject

    canonical_writes = tuple(sorted(writes, key=lambda write: write.key))
    for index in range(1, len(canonical_writes)):
        if canonical_writes[index - 1].key == canonical_writes[index].key:
            duplicate_key = canonical_writes[index].key
            return _reject(
                BalancePatchCodeV1.DUPLICATE_WRITE,
                ("writes", "key", duplicate_key[0], duplicate_key[1]),
            )
    for index, write in enumerate(canonical_writes):
        if _write_is_noop(write):
            return _reject(BalancePatchCodeV1.NO_OP_WRITE, ("writes", index))
    return BalancePatchBuildOkV1(CanonicalBalancePatchV1(canonical_writes))


def _validated_patch_writes_v1(
    patch: object,
) -> tuple[BalanceWriteV1, ...] | BalancePatchRejectV1:
    if type(patch) is not CanonicalBalancePatchV1:
        return _reject(BalancePatchCodeV1.WRONG_EXACT_TYPE, ())
    try:
        writes = object.__getattribute__(patch, "writes")
    except AttributeError:
        return _reject(BalancePatchCodeV1.NONCANONICAL_PATCH, ("writes",))
    reject = _canonical_writes_reject(
        writes,
        invalid_code=BalancePatchCodeV1.NONCANONICAL_PATCH,
    )
    if reject is not None:
        return reject
    return cast(tuple[BalanceWriteV1, ...], writes)


def _invalid_prestate(path: BalancePatchPathV1) -> BalancePatchRejectV1:
    return _reject(BalancePatchCodeV1.INVALID_PRESTATE, path)


def _validated_balance_entries_v1(
    pre: CommittedBalanceTableV1,
) -> tuple[tuple[BalanceKeyV1, int], ...] | BalancePatchRejectV1:
    if type(pre) is not CommittedBalanceTableV1:
        return _reject(BalancePatchCodeV1.WRONG_EXACT_TYPE, ())
    try:
        balances = object.__getattribute__(pre, "_balances")
    except AttributeError:
        return _invalid_prestate(("state", "balances"))
    if type(balances) is not OwnedMapV1:
        return _invalid_prestate(("state", "balances"))
    try:
        revision = object.__getattribute__(balances, "_schema_revision")
        schema_id = object.__getattribute__(balances, "_schema_id")
        entries = object.__getattribute__(balances, "_entries")
        index = object.__getattribute__(balances, "_index")
    except AttributeError:
        return _invalid_prestate(("state", "balances"))
    if type(revision) is not str or type(schema_id) is not str:
        return _invalid_prestate(("state", "balances"))
    if revision != FCIS_STATE_SCHEMA_REVISION_V1 or schema_id != BALANCE_MAP_SCHEMA_ID_V1:
        return _invalid_prestate(("state", "balances"))
    if type(entries) is not tuple or type(index) is not _MAPPING_PROXY_TYPE:
        return _invalid_prestate(("state", "balances"))
    if len(entries) > MAX_BALANCES_V1:
        return _reject(BalancePatchCodeV1.ITEM_LIMIT, ("state", "balances"))

    previous_key: BalanceKeyV1 | None = None
    for entry_index, entry in enumerate(entries):
        entry_path: BalancePatchPathV1 = ("state", "balances", entry_index)
        if type(entry) is not tuple or len(entry) != 2:
            return _invalid_prestate(entry_path)
        key, amount = entry
        key_reject = _balance_key_reject(key, entry_path + ("key",))
        if key_reject is not None:
            return _invalid_prestate(key_reject.path)
        exact_key = cast(BalanceKeyV1, key)
        if type(amount) is not int or amount <= 0:
            return _invalid_prestate(entry_path + ("value",))
        if previous_key is not None and previous_key >= exact_key:
            return _invalid_prestate(entry_path + ("key",))
        previous_key = exact_key

    trusted_index = cast(MappingProxyType, index)
    if len(trusted_index) != len(entries):
        return _invalid_prestate(("state", "balances", "index"))
    index_entries = tuple(trusted_index.items())
    if any(
        observed_key is not expected_key or observed_value is not expected_value
        for (observed_key, observed_value), (expected_key, expected_value) in zip(
            index_entries,
            entries,
            strict=True,
        )
    ):
        return _invalid_prestate(("state", "balances", "index"))
    return cast(tuple[tuple[BalanceKeyV1, int], ...], entries)


def _merge_balance_entries_v1(
    pre_entries: tuple[tuple[BalanceKeyV1, int], ...],
    writes: tuple[BalanceWriteV1, ...],
) -> tuple[tuple[BalanceKeyV1, int], ...] | BalancePatchRejectV1:
    merged: list[tuple[BalanceKeyV1, int]] = []
    pre_index = 0
    for write_index, write in enumerate(writes):
        while pre_index < len(pre_entries) and pre_entries[pre_index][0] < write.key:
            merged.append(pre_entries[pre_index])
            pre_index += 1

        existing = 0
        if pre_index < len(pre_entries) and pre_entries[pre_index][0] == write.key:
            existing = pre_entries[pre_index][1]
        if existing != write.expected_old:
            return _reject(
                BalancePatchCodeV1.EXPECTED_OLD_MISMATCH,
                ("writes", write_index, "expected_old"),
            )
        if write.replacement is not None:
            merged.append((write.key, write.replacement))
        if existing != 0:
            pre_index += 1

    merged.extend(pre_entries[pre_index:])
    if len(merged) > MAX_BALANCES_V1:
        return _reject(BalancePatchCodeV1.ITEM_LIMIT, ("state", "balances"))
    return tuple(merged)


def apply_canonical_balance_patch_v1(
    pre: CommittedBalanceTableV1,
    patch: CanonicalBalancePatchV1,
) -> BalancePatchApplyResultV1:
    """Apply one patch atomically over an immutable balance snapshot.

    Reject returns no candidate. Accept constructs one fresh owned map after
    every compare-and-replace check succeeds. Effects, receipts, roots, and
    storage commitment remain obligations of later core and shell contracts.
    """

    pre_entries = _validated_balance_entries_v1(pre)
    if type(pre_entries) is BalancePatchRejectV1:
        return pre_entries
    writes = _validated_patch_writes_v1(patch)
    if type(writes) is BalancePatchRejectV1:
        return writes
    merged = _merge_balance_entries_v1(pre_entries, writes)
    if type(merged) is BalancePatchRejectV1:
        return merged

    owned = _owned_map_from_canonical_transition_v1(
        merged,
        FCIS_STATE_SCHEMA_REVISION_V1,
        BALANCE_MAP_SCHEMA_ID_V1,
    )
    return BalancePatchApplyOkV1(CommittedBalanceTableV1(owned))


__all__ = [
    "BalanceDeltaV1",
    "BalancePatchApplyOkV1",
    "BalancePatchApplyResultV1",
    "BalancePatchBuildOkV1",
    "BalancePatchBuildResultV1",
    "BalancePatchCodeV1",
    "BalancePatchRejectV1",
    "BalanceWriteV1",
    "CanonicalBalancePatchV1",
    "apply_balance_deltas_v1",
    "apply_canonical_balance_patch_v1",
    "build_canonical_balance_patch_v1",
]
