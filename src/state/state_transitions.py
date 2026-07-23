"""Pure return-new transitions over exact FCIS committed state values.

The implemented slices define canonical balance and nonce patch relations. They do
not expose mutable projections, depend on collection-library tree shape, emit
effects, or commit storage. Those remain separate contracts.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from types import MappingProxyType
from typing import TypeAlias, cast, final

from .canonical import canonical_hex_fixed_allow_0x
from .owned_collections import (
    OwnedMapV1,
    _owned_map_from_canonical_transition_v1,
)
from .snapshot_combinators import MAX_CANONICAL_BYTES_V1
from .state_snapshot_values import (
    BALANCE_MAP_SCHEMA_ID_V1,
    FCIS_STATE_SCHEMA_REVISION_V1,
    MAX_BALANCES_V1,
    MAX_NONCES_V1,
    MAX_STATE_STRING_CHARACTERS_V1,
    MAX_STATE_STRING_UTF8_BYTES_V1,
    MAX_U32_V1,
    NONCE_MAP_SCHEMA_ID_V1,
    BalanceKeyV1,
    CommittedBalanceTableV1,
    CommittedNonceTableV1,
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
        reject for delta in deltas if (reject := _delta_representation_reject(delta)) is not None
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


NoncePatchPathPartV1: TypeAlias = str | int
NoncePatchPathV1: TypeAlias = tuple[NoncePatchPathPartV1, ...]


class NoncePatchCodeV1(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    ITEM_LIMIT = "item_limit"
    NONCANONICAL_KEY = "noncanonical_key"
    OUT_OF_RANGE = "out_of_range"
    EMPTY_PATCH = "empty_patch"
    DUPLICATE_ADVANCE = "duplicate_advance"
    NONCANONICAL_PATCH = "noncanonical_patch"
    EXPECTED_OLD_MISMATCH = "expected_old_mismatch"
    INVALID_PRESTATE = "invalid_prestate"


@final
@dataclass(frozen=True, slots=True)
class NoncePatchRejectV1:
    """Typed no-output rejection for nonce-patch construction or application."""

    code: NoncePatchCodeV1
    path: NoncePatchPathV1


def _nonce_reject(
    code: NoncePatchCodeV1,
    path: NoncePatchPathV1,
) -> NoncePatchRejectV1:
    return NoncePatchRejectV1(code, path)


def _canonical_pubkey_reject_v1(
    pubkey: object,
    path: NoncePatchPathV1,
) -> NoncePatchRejectV1 | None:
    if type(pubkey) is not str:
        return _nonce_reject(NoncePatchCodeV1.WRONG_EXACT_TYPE, path)
    try:
        canonical = canonical_hex_fixed_allow_0x(pubkey, nbytes=48, name="pubkey")
    except (TypeError, ValueError):
        return _nonce_reject(NoncePatchCodeV1.NONCANONICAL_KEY, path)
    if canonical != pubkey:
        return _nonce_reject(NoncePatchCodeV1.NONCANONICAL_KEY, path)
    return None


@final
@dataclass(frozen=True, slots=True)
class NonceAdvanceV1:
    """One strictly monotone compare-and-replace nonce advance.

    Contiguous per-intent batch policy is a prior validation obligation. One
    accepted batch may advance a sender by more than one nonce.
    """

    pubkey: str
    expected_last: int
    new_last: int

    def __post_init__(self) -> None:
        key_reject = _canonical_pubkey_reject_v1(self.pubkey, ("pubkey",))
        if key_reject is not None:
            if key_reject.code is NoncePatchCodeV1.WRONG_EXACT_TYPE:
                raise TypeError("nonce pubkey must be an exact string")
            raise ValueError("nonce pubkey must be canonical fixed-width hex")
        if type(self.expected_last) is not int or not 0 <= self.expected_last <= MAX_U32_V1:
            raise TypeError("expected_last must be an exact u32")
        if type(self.new_last) is not int or not 1 <= self.new_last <= MAX_U32_V1:
            raise TypeError("new_last must be an exact positive u32")
        if self.new_last <= self.expected_last:
            raise ValueError("new_last must strictly advance expected_last")


def _nonce_advance_reject_v1(
    advance: object,
    path: NoncePatchPathV1,
) -> NoncePatchRejectV1 | None:
    if type(advance) is not NonceAdvanceV1:
        return _nonce_reject(NoncePatchCodeV1.WRONG_EXACT_TYPE, path)
    key_reject = _canonical_pubkey_reject_v1(advance.pubkey, path + ("pubkey",))
    if key_reject is not None:
        return key_reject
    if type(advance.expected_last) is not int:
        return _nonce_reject(
            NoncePatchCodeV1.WRONG_EXACT_TYPE,
            path + ("expected_last",),
        )
    if not 0 <= advance.expected_last <= MAX_U32_V1:
        return _nonce_reject(NoncePatchCodeV1.OUT_OF_RANGE, path + ("expected_last",))
    if type(advance.new_last) is not int:
        return _nonce_reject(NoncePatchCodeV1.WRONG_EXACT_TYPE, path + ("new_last",))
    if not 1 <= advance.new_last <= MAX_U32_V1:
        return _nonce_reject(NoncePatchCodeV1.OUT_OF_RANGE, path + ("new_last",))
    if advance.new_last <= advance.expected_last:
        return _nonce_reject(NoncePatchCodeV1.OUT_OF_RANGE, path + ("new_last",))
    return None


def _canonical_nonce_advances_reject_v1(
    advances: object,
    *,
    invalid_code: NoncePatchCodeV1,
) -> NoncePatchRejectV1 | None:
    if type(advances) is not tuple or not advances:
        return _nonce_reject(invalid_code, ("advances",))
    if len(advances) > MAX_NONCES_V1:
        return _nonce_reject(NoncePatchCodeV1.ITEM_LIMIT, ("advances",))

    previous_pubkey: str | None = None
    for index, advance in enumerate(advances):
        path: NoncePatchPathV1 = ("advances", index)
        representation_reject = _nonce_advance_reject_v1(advance, path)
        if representation_reject is not None:
            return _nonce_reject(invalid_code, representation_reject.path)
        exact_advance = cast(NonceAdvanceV1, advance)
        if previous_pubkey is not None and previous_pubkey >= exact_advance.pubkey:
            return _nonce_reject(invalid_code, path + ("pubkey",))
        previous_pubkey = exact_advance.pubkey
    return None


@final
@dataclass(frozen=True, slots=True)
class CanonicalNoncePatchV1:
    """Nonempty, pubkey-sorted, duplicate-free monotone nonce advances."""

    advances: tuple[NonceAdvanceV1, ...]

    def __post_init__(self) -> None:
        reject = _canonical_nonce_advances_reject_v1(
            self.advances,
            invalid_code=NoncePatchCodeV1.NONCANONICAL_PATCH,
        )
        if reject is not None:
            raise ValueError("CanonicalNoncePatchV1 requires canonical advances")


@final
@dataclass(frozen=True, slots=True)
class NoncePatchBuildOkV1:
    patch: CanonicalNoncePatchV1


@final
@dataclass(frozen=True, slots=True)
class NoncePatchApplyOkV1:
    state: CommittedNonceTableV1


NoncePatchBuildResultV1 = NoncePatchBuildOkV1 | NoncePatchRejectV1
NoncePatchApplyResultV1 = NoncePatchApplyOkV1 | NoncePatchRejectV1


def build_canonical_nonce_patch_v1(
    advances: tuple[NonceAdvanceV1, ...],
) -> NoncePatchBuildResultV1:
    """Canonicalize exact per-sender advances without consulting state."""

    if type(advances) is not tuple:
        return _nonce_reject(NoncePatchCodeV1.WRONG_EXACT_TYPE, ("advances",))
    if not advances:
        return _nonce_reject(NoncePatchCodeV1.EMPTY_PATCH, ("advances",))
    if len(advances) > MAX_NONCES_V1:
        return _nonce_reject(NoncePatchCodeV1.ITEM_LIMIT, ("advances",))

    for index, advance in enumerate(advances):
        representation_reject = _nonce_advance_reject_v1(advance, ("advances", index))
        if representation_reject is not None:
            return representation_reject

    canonical = tuple(sorted(advances, key=lambda advance: advance.pubkey))
    for index in range(1, len(canonical)):
        if canonical[index - 1].pubkey == canonical[index].pubkey:
            return _nonce_reject(
                NoncePatchCodeV1.DUPLICATE_ADVANCE,
                ("advances", "pubkey", canonical[index].pubkey),
            )
    return NoncePatchBuildOkV1(CanonicalNoncePatchV1(canonical))


def _invalid_nonce_prestate(path: NoncePatchPathV1) -> NoncePatchRejectV1:
    return _nonce_reject(NoncePatchCodeV1.INVALID_PRESTATE, path)


def _validated_nonce_entries_v1(
    pre: CommittedNonceTableV1,
) -> tuple[tuple[str, int], ...] | NoncePatchRejectV1:
    if type(pre) is not CommittedNonceTableV1:
        return _nonce_reject(NoncePatchCodeV1.WRONG_EXACT_TYPE, ())
    try:
        nonces = object.__getattribute__(pre, "_last")
    except AttributeError:
        return _invalid_nonce_prestate(("state", "nonces"))
    if type(nonces) is not OwnedMapV1:
        return _invalid_nonce_prestate(("state", "nonces"))
    try:
        revision = object.__getattribute__(nonces, "_schema_revision")
        schema_id = object.__getattribute__(nonces, "_schema_id")
        entries = object.__getattribute__(nonces, "_entries")
        index = object.__getattribute__(nonces, "_index")
    except AttributeError:
        return _invalid_nonce_prestate(("state", "nonces"))
    if type(revision) is not str or type(schema_id) is not str:
        return _invalid_nonce_prestate(("state", "nonces"))
    if revision != FCIS_STATE_SCHEMA_REVISION_V1 or schema_id != NONCE_MAP_SCHEMA_ID_V1:
        return _invalid_nonce_prestate(("state", "nonces"))
    if type(entries) is not tuple or type(index) is not _MAPPING_PROXY_TYPE:
        return _invalid_nonce_prestate(("state", "nonces"))
    if len(entries) > MAX_NONCES_V1:
        return _nonce_reject(NoncePatchCodeV1.ITEM_LIMIT, ("state", "nonces"))

    previous_pubkey: str | None = None
    for entry_index, entry in enumerate(entries):
        path: NoncePatchPathV1 = ("state", "nonces", entry_index)
        if type(entry) is not tuple or len(entry) != 2:
            return _invalid_nonce_prestate(path)
        pubkey, nonce = entry
        key_reject = _canonical_pubkey_reject_v1(pubkey, path + ("pubkey",))
        if key_reject is not None:
            return _invalid_nonce_prestate(key_reject.path)
        exact_pubkey = cast(str, pubkey)
        if type(nonce) is not int or not 0 <= nonce <= MAX_U32_V1:
            return _invalid_nonce_prestate(path + ("nonce",))
        if previous_pubkey is not None and previous_pubkey >= exact_pubkey:
            return _invalid_nonce_prestate(path + ("pubkey",))
        previous_pubkey = exact_pubkey

    trusted_index = cast(MappingProxyType, index)
    if len(trusted_index) != len(entries):
        return _invalid_nonce_prestate(("state", "nonces", "index"))
    index_entries = tuple(trusted_index.items())
    if any(
        observed_key is not expected_key or observed_value is not expected_value
        for (observed_key, observed_value), (expected_key, expected_value) in zip(
            index_entries,
            entries,
            strict=True,
        )
    ):
        return _invalid_nonce_prestate(("state", "nonces", "index"))
    return cast(tuple[tuple[str, int], ...], entries)


def _validated_nonce_patch_advances_v1(
    patch: object,
) -> tuple[NonceAdvanceV1, ...] | NoncePatchRejectV1:
    if type(patch) is not CanonicalNoncePatchV1:
        return _nonce_reject(NoncePatchCodeV1.WRONG_EXACT_TYPE, ())
    try:
        advances = object.__getattribute__(patch, "advances")
    except AttributeError:
        return _nonce_reject(NoncePatchCodeV1.NONCANONICAL_PATCH, ("advances",))
    reject = _canonical_nonce_advances_reject_v1(
        advances,
        invalid_code=NoncePatchCodeV1.NONCANONICAL_PATCH,
    )
    if reject is not None:
        return reject
    return cast(tuple[NonceAdvanceV1, ...], advances)


def _merge_nonce_entries_v1(
    pre_entries: tuple[tuple[str, int], ...],
    advances: tuple[NonceAdvanceV1, ...],
) -> tuple[tuple[str, int], ...] | NoncePatchRejectV1:
    merged: list[tuple[str, int]] = []
    pre_index = 0
    for advance_index, advance in enumerate(advances):
        while pre_index < len(pre_entries) and pre_entries[pre_index][0] < advance.pubkey:
            merged.append(pre_entries[pre_index])
            pre_index += 1

        found_existing = (
            pre_index < len(pre_entries) and pre_entries[pre_index][0] == advance.pubkey
        )
        existing = 0
        if found_existing:
            existing = pre_entries[pre_index][1]
        if existing != advance.expected_last:
            return _nonce_reject(
                NoncePatchCodeV1.EXPECTED_OLD_MISMATCH,
                ("advances", advance_index, "expected_last"),
            )
        merged.append((advance.pubkey, advance.new_last))
        if found_existing:
            pre_index += 1

    merged.extend(pre_entries[pre_index:])
    if len(merged) > MAX_NONCES_V1:
        return _nonce_reject(NoncePatchCodeV1.ITEM_LIMIT, ("state", "nonces"))
    return tuple(merged)


def apply_canonical_nonce_patch_v1(
    pre: CommittedNonceTableV1,
    patch: CanonicalNoncePatchV1,
) -> NoncePatchApplyResultV1:
    """Apply a complete nonce patch atomically over one immutable snapshot."""

    pre_entries = _validated_nonce_entries_v1(pre)
    if type(pre_entries) is NoncePatchRejectV1:
        return pre_entries
    advances = _validated_nonce_patch_advances_v1(patch)
    if type(advances) is NoncePatchRejectV1:
        return advances
    merged = _merge_nonce_entries_v1(pre_entries, advances)
    if type(merged) is NoncePatchRejectV1:
        return merged

    owned = _owned_map_from_canonical_transition_v1(
        merged,
        FCIS_STATE_SCHEMA_REVISION_V1,
        NONCE_MAP_SCHEMA_ID_V1,
    )
    return NoncePatchApplyOkV1(CommittedNonceTableV1(owned))


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
    "CanonicalNoncePatchV1",
    "NonceAdvanceV1",
    "NoncePatchApplyOkV1",
    "NoncePatchApplyResultV1",
    "NoncePatchBuildOkV1",
    "NoncePatchBuildResultV1",
    "NoncePatchCodeV1",
    "NoncePatchRejectV1",
    "apply_balance_deltas_v1",
    "apply_canonical_balance_patch_v1",
    "apply_canonical_nonce_patch_v1",
    "build_canonical_balance_patch_v1",
    "build_canonical_nonce_patch_v1",
]
