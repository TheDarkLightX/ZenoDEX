"""Pure return-new transitions over exact FCIS committed state values.

The implemented slices define canonical balance, nonce, aggregate LP, and pool-map
patch relations. They do not expose mutable projections, depend on
collection-library tree shape, emit effects, or commit storage. Those remain
separate contracts.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from types import MappingProxyType
from typing import TypeAlias, cast, final

from .canonical import bounded_json_utf8_size, canonical_hex_fixed_allow_0x
from .owned_collections import (
    OwnedMapV1,
    _owned_map_from_canonical_transition_v1,
)
from .snapshot_combinators import MAX_CANONICAL_BYTES_V1, MAX_COLLECTION_ITEMS_V1
from .state_snapshot_values import (
    BALANCE_MAP_SCHEMA_ID_V1,
    DEX_LP_AMOUNT_MAX,
    DEX_LP_SUPPLY_MAX,
    DEX_POOL_RESERVE_MAX,
    FCIS_STATE_SCHEMA_REVISION_V1,
    LP_BALANCE_MAP_SCHEMA_ID_V1,
    LP_CHURN_TIER_MAP_SCHEMA_ID_V1,
    LP_LAST_CHURN_UPDATE_MAP_SCHEMA_ID_V1,
    LP_LAST_MINT_MAP_SCHEMA_ID_V1,
    LP_LAST_REMOVE_MAP_SCHEMA_ID_V1,
    MAX_BALANCES_V1,
    MAX_LP_ENTRIES_V1,
    MAX_NONCES_V1,
    MAX_POOLS_V1,
    MAX_STATE_STRING_CHARACTERS_V1,
    MAX_STATE_STRING_UTF8_BYTES_V1,
    MAX_U32_V1,
    NONCE_MAP_SCHEMA_ID_V1,
    PERPS_ISOLATED_ACCOUNT_MAP_SCHEMA_ID_V1,
    PERPS_ISOLATED_GLOBAL_MAP_SCHEMA_ID_V1,
    POOL_MAP_SCHEMA_ID_V1,
    BalanceKeyV1,
    CommittedBalanceTableV1,
    CommittedLPTableV1,
    CommittedNonceTableV1,
    CommittedPerpAccountStateV1,
    CommittedPerpMarketStateV1,
    CommittedPoolStateV1,
    LPKeyV1,
    PerpsValueV1,
)


def _committed_isolated_market_from_transition_v1(
    pre: CommittedPerpMarketStateV1,
    global_entries: tuple[tuple[str, PerpsValueV1], ...],
) -> CommittedPerpMarketStateV1:
    """Trusted freeze edge for a fully evaluated isolated-market successor.

    The caller is a closed exact transition. Only an immutable canonical tuple
    crosses the module boundary; the caller's private work buffer does not.
    The committed constructor rechecks the full market and account invariants
    before the candidate can escape.
    """

    if type(pre) is not CommittedPerpMarketStateV1:
        raise TypeError("isolated market pre-state must be exact")
    if type(global_entries) is not tuple:
        raise TypeError("isolated market globals must be an exact tuple")
    globals_owned = _owned_map_from_canonical_transition_v1(
        global_entries,
        FCIS_STATE_SCHEMA_REVISION_V1,
        PERPS_ISOLATED_GLOBAL_MAP_SCHEMA_ID_V1,
    )
    return CommittedPerpMarketStateV1(
        quote_asset=pre.quote_asset,
        global_state=globals_owned,
        accounts=pre.accounts,
        kind=pre.kind,
    )


def _committed_isolated_market_with_accounts_from_transition_v1(
    pre: CommittedPerpMarketStateV1,
    account_entries: tuple[tuple[str, CommittedPerpAccountStateV1], ...],
) -> CommittedPerpMarketStateV1:
    """Trusted freeze edge for canonical isolated-account successors.

    Only the immutable account-entry tuple crosses the module boundary. The
    unchanged exact global map is structurally shared with the pre-state.
    """

    if type(pre) is not CommittedPerpMarketStateV1:
        raise TypeError("isolated market pre-state must be exact")
    if type(account_entries) is not tuple:
        raise TypeError("isolated market accounts must be an exact tuple")
    accounts_owned = _owned_map_from_canonical_transition_v1(
        account_entries,
        FCIS_STATE_SCHEMA_REVISION_V1,
        PERPS_ISOLATED_ACCOUNT_MAP_SCHEMA_ID_V1,
    )
    return CommittedPerpMarketStateV1(
        quote_asset=pre.quote_asset,
        global_state=pre.global_state,
        accounts=accounts_owned,
        kind=pre.kind,
    )


def _committed_isolated_market_with_globals_and_accounts_from_transition_v1(
    pre: CommittedPerpMarketStateV1,
    global_entries: tuple[tuple[str, PerpsValueV1], ...],
    account_entries: tuple[tuple[str, CommittedPerpAccountStateV1], ...],
) -> CommittedPerpMarketStateV1:
    """Trusted freeze edge for one atomic global-and-account successor.

    Some isolated-perps actions, including partial liquidation, update an
    account and protocol accumulators in the same transition.  Both canonical
    entry tuples must therefore cross one freeze edge and be revalidated as a
    single committed market.  Neither a globals-only nor an accounts-only
    candidate is constructed or exposed.
    """

    if type(pre) is not CommittedPerpMarketStateV1:
        raise TypeError("isolated market pre-state must be exact")
    if type(global_entries) is not tuple:
        raise TypeError("isolated market globals must be an exact tuple")
    if type(account_entries) is not tuple:
        raise TypeError("isolated market accounts must be an exact tuple")
    globals_owned = _owned_map_from_canonical_transition_v1(
        global_entries,
        FCIS_STATE_SCHEMA_REVISION_V1,
        PERPS_ISOLATED_GLOBAL_MAP_SCHEMA_ID_V1,
    )
    accounts_owned = _owned_map_from_canonical_transition_v1(
        account_entries,
        FCIS_STATE_SCHEMA_REVISION_V1,
        PERPS_ISOLATED_ACCOUNT_MAP_SCHEMA_ID_V1,
    )
    return CommittedPerpMarketStateV1(
        quote_asset=pre.quote_asset,
        global_state=globals_owned,
        accounts=accounts_owned,
        kind=pre.kind,
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
            key_component = self.key[cast(int, key_reject.path[-1])]
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
    patch: CanonicalBalancePatchV1 | None


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


def validate_balance_deltas_v1(
    deltas: object,
) -> BalancePatchRejectV1 | None:
    """Validate one unordered balance-delta family without reading state."""

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
    for delta in cast(tuple[BalanceDeltaV1, ...], deltas):
        work_bytes += len(delta.key[0].encode("utf-8"))
        work_bytes += len(delta.key[1].encode("utf-8"))
        work_bytes += max(1, (abs(delta.net_delta).bit_length() + 7) // 8)
        if work_bytes > MAX_CANONICAL_BYTES_V1:
            return _reject(BalancePatchCodeV1.BYTE_LIMIT, ("deltas",))
    return None


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
    delta_reject = validate_balance_deltas_v1(deltas)
    if delta_reject is not None:
        return delta_reject

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
        return BalancePatchApplyOkV1(pre, None)
    patch_result = build_canonical_balance_patch_v1(tuple(writes))
    if type(patch_result) is BalancePatchRejectV1:
        return patch_result
    return apply_canonical_balance_patch_v1(pre, patch_result.patch)


def validate_committed_balance_state_v1(
    pre: CommittedBalanceTableV1,
) -> BalancePatchRejectV1 | None:
    """Revalidate one exact balance state before any authority-bearing read."""

    entries = _validated_balance_entries_v1(pre)
    if type(entries) is BalancePatchRejectV1:
        return entries
    return None


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
    return BalancePatchApplyOkV1(CommittedBalanceTableV1(owned), patch)


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
    patch: CanonicalNoncePatchV1 | None


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


def validate_committed_nonce_state_v1(
    pre: CommittedNonceTableV1,
) -> NoncePatchRejectV1 | None:
    """Revalidate one exact nonce snapshot without constructing a patch."""

    validated = _validated_nonce_entries_v1(pre)
    if type(validated) is NoncePatchRejectV1:
        return validated
    return None


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
    return NoncePatchApplyOkV1(CommittedNonceTableV1(owned), patch)


LPPositionPatchPathPartV1: TypeAlias = str | int
LPPositionPatchPathV1: TypeAlias = tuple[LPPositionPatchPathPartV1, ...]
_LP_MAP_SCHEMA_IDS_V1 = (
    LP_BALANCE_MAP_SCHEMA_ID_V1,
    LP_LAST_MINT_MAP_SCHEMA_ID_V1,
    LP_LAST_REMOVE_MAP_SCHEMA_ID_V1,
    LP_CHURN_TIER_MAP_SCHEMA_ID_V1,
    LP_LAST_CHURN_UPDATE_MAP_SCHEMA_ID_V1,
)


class LPPositionPatchCodeV1(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    ITEM_LIMIT = "item_limit"
    BYTE_LIMIT = "byte_limit"
    NONCANONICAL_KEY = "noncanonical_key"
    OUT_OF_RANGE = "out_of_range"
    DOMAIN_INVARIANT = "domain_invariant"
    EMPTY_PATCH = "empty_patch"
    DUPLICATE_WRITE = "duplicate_write"
    NO_OP_WRITE = "no_op_write"
    NONCANONICAL_PATCH = "noncanonical_patch"
    EXPECTED_OLD_MISMATCH = "expected_old_mismatch"
    INVALID_PRESTATE = "invalid_prestate"
    INVALID_CANDIDATE = "invalid_candidate"


@final
@dataclass(frozen=True, slots=True)
class LPPositionPatchRejectV1:
    """Typed no-output rejection for one aggregate LP-position patch."""

    code: LPPositionPatchCodeV1
    path: LPPositionPatchPathV1


def _lp_reject(
    code: LPPositionPatchCodeV1,
    path: LPPositionPatchPathV1,
) -> LPPositionPatchRejectV1:
    return LPPositionPatchRejectV1(code, path)


def _lp_key_reject_v1(
    key: object,
    path: LPPositionPatchPathV1,
) -> LPPositionPatchRejectV1 | None:
    if type(key) is not tuple or len(key) != 2:
        return _lp_reject(LPPositionPatchCodeV1.WRONG_EXACT_TYPE, path)
    for index, component in enumerate(key):
        component_path = path + (index,)
        if type(component) is not str:
            return _lp_reject(LPPositionPatchCodeV1.WRONG_EXACT_TYPE, component_path)
        if not component:
            return _lp_reject(LPPositionPatchCodeV1.NONCANONICAL_KEY, component_path)
        if len(component) > MAX_STATE_STRING_CHARACTERS_V1:
            return _lp_reject(LPPositionPatchCodeV1.ITEM_LIMIT, component_path)
        try:
            encoded = component.encode("utf-8")
        except UnicodeEncodeError:
            return _lp_reject(LPPositionPatchCodeV1.NONCANONICAL_KEY, component_path)
        if len(encoded) > MAX_STATE_STRING_UTF8_BYTES_V1:
            return _lp_reject(LPPositionPatchCodeV1.ITEM_LIMIT, component_path)
    return None


def _optional_nonnegative_int_reject_v1(
    value: object,
    path: LPPositionPatchPathV1,
) -> LPPositionPatchRejectV1 | None:
    if value is None:
        return None
    if type(value) is not int:
        return _lp_reject(LPPositionPatchCodeV1.WRONG_EXACT_TYPE, path)
    if value < 0:
        return _lp_reject(LPPositionPatchCodeV1.OUT_OF_RANGE, path)
    return None


@final
@dataclass(frozen=True, slots=True)
class LPPositionValueV1:
    """Complete semantic value for one LP balance and duration-risk key."""

    balance: int = 0
    last_mint_timestamp: int | None = None
    last_remove_timestamp: int | None = None
    churn_tier: int = 0
    last_churn_update_timestamp: int | None = None

    def __post_init__(self) -> None:
        if type(self.balance) is not int:
            raise TypeError("LP position balance must be an exact integer")
        if not 0 <= self.balance <= DEX_LP_AMOUNT_MAX:
            raise ValueError("LP position balance is outside the committed domain")
        for field_name in (
            "last_mint_timestamp",
            "last_remove_timestamp",
            "last_churn_update_timestamp",
        ):
            value = object.__getattribute__(self, field_name)
            if value is not None and type(value) is not int:
                raise TypeError(f"{field_name} must be None or an exact integer")
            if value is not None and value < 0:
                raise ValueError(f"{field_name} must be nonnegative")
        if type(self.churn_tier) is not int:
            raise TypeError("churn_tier must be an exact integer")
        if self.churn_tier < 0:
            raise ValueError("churn_tier must be nonnegative")
        if self.last_mint_timestamp is not None and self.balance == 0:
            raise ValueError("last_mint_timestamp requires a positive LP balance")


_EMPTY_LP_POSITION_V1 = LPPositionValueV1()


@final
@dataclass(frozen=True, slots=True)
class LPPositionDeltaV1:
    """One exact additive LP-balance atom for canonical reduction.

    Duration-risk metadata is part of the aggregate position value and is
    preserved by this balance-only operation. Burning a position to zero clears
    its last-mint timestamp, matching the mounted ``LPTable.set`` behavior.
    """

    key: LPKeyV1
    net_delta: int

    def __post_init__(self) -> None:
        key_reject = _lp_key_reject_v1(self.key, ("key",))
        if key_reject is not None:
            if key_reject.code is LPPositionPatchCodeV1.WRONG_EXACT_TYPE:
                raise TypeError("LP position delta key must be an exact pair of strings")
            raise ValueError("LP position delta key is not canonical")
        if type(self.net_delta) is not int:
            raise TypeError("LP position net_delta must be an exact integer")
        if self.net_delta == 0:
            raise ValueError("LP position net_delta must be nonzero")


def _lp_position_value_reject_v1(
    value: object,
    path: LPPositionPatchPathV1,
) -> LPPositionPatchRejectV1 | None:
    if type(value) is not LPPositionValueV1:
        return _lp_reject(LPPositionPatchCodeV1.WRONG_EXACT_TYPE, path)
    if type(value.balance) is not int:
        return _lp_reject(LPPositionPatchCodeV1.WRONG_EXACT_TYPE, path + ("balance",))
    if not 0 <= value.balance <= DEX_LP_AMOUNT_MAX:
        return _lp_reject(LPPositionPatchCodeV1.OUT_OF_RANGE, path + ("balance",))
    for field_name in (
        "last_mint_timestamp",
        "last_remove_timestamp",
        "last_churn_update_timestamp",
    ):
        reject = _optional_nonnegative_int_reject_v1(
            object.__getattribute__(value, field_name),
            path + (field_name,),
        )
        if reject is not None:
            return reject
    if type(value.churn_tier) is not int:
        return _lp_reject(LPPositionPatchCodeV1.WRONG_EXACT_TYPE, path + ("churn_tier",))
    if value.churn_tier < 0:
        return _lp_reject(LPPositionPatchCodeV1.OUT_OF_RANGE, path + ("churn_tier",))
    if value.last_mint_timestamp is not None and value.balance == 0:
        return _lp_reject(LPPositionPatchCodeV1.DOMAIN_INVARIANT, path)
    return None


@final
@dataclass(frozen=True, slots=True)
class LPPositionWriteV1:
    """Compare-and-replace all five committed maps for one LP position key."""

    key: LPKeyV1
    expected: LPPositionValueV1
    replacement: LPPositionValueV1

    def __post_init__(self) -> None:
        key_reject = _lp_key_reject_v1(self.key, ("key",))
        if key_reject is not None:
            if key_reject.code is LPPositionPatchCodeV1.WRONG_EXACT_TYPE:
                raise TypeError("LP position key must be an exact pair of strings")
            raise ValueError("LP position key is not canonical")
        for field_name in ("expected", "replacement"):
            value_reject = _lp_position_value_reject_v1(
                object.__getattribute__(self, field_name),
                (field_name,),
            )
            if value_reject is not None:
                if value_reject.code is LPPositionPatchCodeV1.WRONG_EXACT_TYPE:
                    raise TypeError(f"{field_name} must be an exact LPPositionValueV1")
                raise ValueError(f"{field_name} violates the LP position domain")


def _lp_write_reject_v1(
    write: object,
    path: LPPositionPatchPathV1,
) -> LPPositionPatchRejectV1 | None:
    if type(write) is not LPPositionWriteV1:
        return _lp_reject(LPPositionPatchCodeV1.WRONG_EXACT_TYPE, path)
    key_reject = _lp_key_reject_v1(write.key, path + ("key",))
    if key_reject is not None:
        return key_reject
    expected_reject = _lp_position_value_reject_v1(write.expected, path + ("expected",))
    if expected_reject is not None:
        return expected_reject
    return _lp_position_value_reject_v1(write.replacement, path + ("replacement",))


def _lp_write_work_bytes_v1(write: LPPositionWriteV1) -> int:
    total = len(write.key[0].encode("utf-8")) + len(write.key[1].encode("utf-8"))
    for value in (write.expected, write.replacement):
        for scalar in (
            value.balance,
            value.last_mint_timestamp,
            value.last_remove_timestamp,
            value.churn_tier,
            value.last_churn_update_timestamp,
        ):
            if scalar is not None:
                total += max(1, (scalar.bit_length() + 7) // 8)
    return total


def _canonical_lp_writes_reject_v1(
    writes: object,
    *,
    invalid_code: LPPositionPatchCodeV1,
) -> LPPositionPatchRejectV1 | None:
    if type(writes) is not tuple or not writes:
        return _lp_reject(invalid_code, ("writes",))
    if len(writes) > MAX_LP_ENTRIES_V1:
        return _lp_reject(LPPositionPatchCodeV1.ITEM_LIMIT, ("writes",))

    previous_key: LPKeyV1 | None = None
    work_bytes = 0
    for index, write in enumerate(writes):
        path: LPPositionPatchPathV1 = ("writes", index)
        representation_reject = _lp_write_reject_v1(write, path)
        if representation_reject is not None:
            return _lp_reject(invalid_code, representation_reject.path)
        exact_write = cast(LPPositionWriteV1, write)
        if exact_write.expected == exact_write.replacement:
            return _lp_reject(invalid_code, path)
        if previous_key is not None and previous_key >= exact_write.key:
            return _lp_reject(invalid_code, path + ("key",))
        previous_key = exact_write.key
        work_bytes += _lp_write_work_bytes_v1(exact_write)
        if work_bytes > MAX_CANONICAL_BYTES_V1:
            return _lp_reject(LPPositionPatchCodeV1.BYTE_LIMIT, ("writes",))
    return None


@final
@dataclass(frozen=True, slots=True)
class CanonicalLPPositionPatchV1:
    """Sorted duplicate-free complete writes over aggregate LP positions."""

    writes: tuple[LPPositionWriteV1, ...]

    def __post_init__(self) -> None:
        reject = _canonical_lp_writes_reject_v1(
            self.writes,
            invalid_code=LPPositionPatchCodeV1.NONCANONICAL_PATCH,
        )
        if reject is not None:
            raise ValueError("CanonicalLPPositionPatchV1 requires canonical writes")


@final
@dataclass(frozen=True, slots=True)
class LPPositionPatchBuildOkV1:
    patch: CanonicalLPPositionPatchV1


@final
@dataclass(frozen=True, slots=True)
class LPPositionPatchApplyOkV1:
    state: CommittedLPTableV1
    patch: CanonicalLPPositionPatchV1 | None


LPPositionPatchBuildResultV1 = LPPositionPatchBuildOkV1 | LPPositionPatchRejectV1
LPPositionPatchApplyResultV1 = LPPositionPatchApplyOkV1 | LPPositionPatchRejectV1


def build_canonical_lp_position_patch_v1(
    writes: tuple[LPPositionWriteV1, ...],
) -> LPPositionPatchBuildResultV1:
    """Canonicalize complete LP-position writes before consulting pre-state."""

    if type(writes) is not tuple:
        return _lp_reject(LPPositionPatchCodeV1.WRONG_EXACT_TYPE, ("writes",))
    if not writes:
        return _lp_reject(LPPositionPatchCodeV1.EMPTY_PATCH, ("writes",))
    if len(writes) > MAX_LP_ENTRIES_V1:
        return _lp_reject(LPPositionPatchCodeV1.ITEM_LIMIT, ("writes",))

    work_bytes = 0
    for index, write in enumerate(writes):
        representation_reject = _lp_write_reject_v1(write, ("writes", index))
        if representation_reject is not None:
            return representation_reject
        work_bytes += _lp_write_work_bytes_v1(write)
        if work_bytes > MAX_CANONICAL_BYTES_V1:
            return _lp_reject(LPPositionPatchCodeV1.BYTE_LIMIT, ("writes",))

    canonical = tuple(sorted(writes, key=lambda write: write.key))
    for index in range(1, len(canonical)):
        if canonical[index - 1].key == canonical[index].key:
            duplicate_key = canonical[index].key
            return _lp_reject(
                LPPositionPatchCodeV1.DUPLICATE_WRITE,
                ("writes", "key", duplicate_key[0], duplicate_key[1]),
            )
    for index, write in enumerate(canonical):
        if write.expected == write.replacement:
            return _lp_reject(LPPositionPatchCodeV1.NO_OP_WRITE, ("writes", index))
    return LPPositionPatchBuildOkV1(CanonicalLPPositionPatchV1(canonical))


def _lp_positions_from_committed_v1(
    pre: CommittedLPTableV1,
) -> dict[LPKeyV1, LPPositionValueV1] | LPPositionPatchRejectV1:
    from .state_snapshots import StateAdmissionError, snapshot_lp_table

    if type(pre) is not CommittedLPTableV1:
        return _lp_reject(LPPositionPatchCodeV1.WRONG_EXACT_TYPE, ())
    try:
        admitted = snapshot_lp_table(pre)
    except StateAdmissionError as exc:
        return _lp_reject(LPPositionPatchCodeV1.INVALID_PRESTATE, ("state",) + exc.path)

    positions: dict[LPKeyV1, LPPositionValueV1] = {
        key: LPPositionValueV1(balance=amount) for key, amount in admitted.balance_entries
    }
    for key, timestamp in admitted.last_mint_entries:
        positions[key] = replace(
            positions.get(key, _EMPTY_LP_POSITION_V1), last_mint_timestamp=timestamp
        )
    for key, timestamp in admitted.last_remove_entries:
        positions[key] = replace(
            positions.get(key, _EMPTY_LP_POSITION_V1),
            last_remove_timestamp=timestamp,
        )
    for key, tier in admitted.churn_tier_entries:
        positions[key] = replace(positions.get(key, _EMPTY_LP_POSITION_V1), churn_tier=tier)
    for key, timestamp in admitted.last_churn_update_entries:
        positions[key] = replace(
            positions.get(key, _EMPTY_LP_POSITION_V1),
            last_churn_update_timestamp=timestamp,
        )
    return positions


def _validated_lp_patch_writes_v1(
    patch: object,
) -> tuple[LPPositionWriteV1, ...] | LPPositionPatchRejectV1:
    if type(patch) is not CanonicalLPPositionPatchV1:
        return _lp_reject(LPPositionPatchCodeV1.WRONG_EXACT_TYPE, ())
    try:
        writes = object.__getattribute__(patch, "writes")
    except AttributeError:
        return _lp_reject(LPPositionPatchCodeV1.NONCANONICAL_PATCH, ("writes",))
    reject = _canonical_lp_writes_reject_v1(
        writes,
        invalid_code=LPPositionPatchCodeV1.NONCANONICAL_PATCH,
    )
    if reject is not None:
        return reject
    return cast(tuple[LPPositionWriteV1, ...], writes)


def _candidate_lp_table_v1(
    positions: dict[LPKeyV1, LPPositionValueV1],
) -> CommittedLPTableV1 | LPPositionPatchRejectV1:
    position_items = tuple(sorted(positions.items(), key=lambda item: item[0]))
    balance_entries = tuple(
        (key, value.balance) for key, value in position_items if value.balance > 0
    )
    last_mint_entries = tuple(
        (key, value.last_mint_timestamp)
        for key, value in position_items
        if value.last_mint_timestamp is not None
    )
    last_remove_entries = tuple(
        (key, value.last_remove_timestamp)
        for key, value in position_items
        if value.last_remove_timestamp is not None
    )
    churn_tier_entries = tuple(
        (key, value.churn_tier) for key, value in position_items if value.churn_tier > 0
    )
    last_churn_update_entries = tuple(
        (key, value.last_churn_update_timestamp)
        for key, value in position_items
        if value.last_churn_update_timestamp is not None
    )
    entry_groups = (
        balance_entries,
        last_mint_entries,
        last_remove_entries,
        churn_tier_entries,
        last_churn_update_entries,
    )
    if sum(len(entries) for entries in entry_groups) > MAX_LP_ENTRIES_V1:
        return _lp_reject(LPPositionPatchCodeV1.ITEM_LIMIT, ("state", "lp_balances"))

    try:
        owned_maps = tuple(
            _owned_map_from_canonical_transition_v1(
                entries,
                FCIS_STATE_SCHEMA_REVISION_V1,
                schema_id,
            )
            for entries, schema_id in zip(entry_groups, _LP_MAP_SCHEMA_IDS_V1, strict=True)
        )
        candidate = CommittedLPTableV1(
            owned_maps[0],
            owned_maps[1],
            owned_maps[2],
            owned_maps[3],
            owned_maps[4],
        )
    except (TypeError, ValueError):
        return _lp_reject(LPPositionPatchCodeV1.INVALID_CANDIDATE, ("state", "lp_balances"))
    return _revalidate_lp_candidate_v1(candidate)


def _revalidate_lp_candidate_v1(
    candidate: CommittedLPTableV1,
) -> CommittedLPTableV1 | LPPositionPatchRejectV1:
    """Run the one closed admission boundary over the completed candidate."""

    from .state_snapshots import StateAdmissionError, snapshot_lp_table

    try:
        return snapshot_lp_table(candidate)
    except StateAdmissionError as exc:
        return _lp_reject(LPPositionPatchCodeV1.INVALID_CANDIDATE, ("state",) + exc.path)


def apply_canonical_lp_position_patch_v1(
    pre: CommittedLPTableV1,
    patch: CanonicalLPPositionPatchV1,
) -> LPPositionPatchApplyResultV1:
    """Apply all balance and duration-risk fields as one immutable candidate."""

    positions = _lp_positions_from_committed_v1(pre)
    if type(positions) is LPPositionPatchRejectV1:
        return positions
    writes = _validated_lp_patch_writes_v1(patch)
    if type(writes) is LPPositionPatchRejectV1:
        return writes

    updated = dict(positions)
    for index, write in enumerate(writes):
        current = updated.get(write.key, _EMPTY_LP_POSITION_V1)
        if current != write.expected:
            return _lp_reject(
                LPPositionPatchCodeV1.EXPECTED_OLD_MISMATCH,
                ("writes", index, "expected"),
            )
        if write.replacement == _EMPTY_LP_POSITION_V1:
            updated.pop(write.key, None)
        else:
            updated[write.key] = write.replacement

    candidate = _candidate_lp_table_v1(updated)
    if type(candidate) is LPPositionPatchRejectV1:
        return candidate
    return LPPositionPatchApplyOkV1(candidate, patch)


def _lp_delta_reject_v1(delta: object) -> LPPositionPatchRejectV1 | None:
    if type(delta) is not LPPositionDeltaV1:
        return _lp_reject(LPPositionPatchCodeV1.WRONG_EXACT_TYPE, ("deltas",))
    key_reject = _lp_key_reject_v1(delta.key, ("deltas", "key"))
    if key_reject is not None:
        return key_reject
    if type(delta.net_delta) is not int:
        return _lp_reject(
            LPPositionPatchCodeV1.WRONG_EXACT_TYPE,
            ("deltas", "net_delta"),
        )
    if delta.net_delta == 0:
        return _lp_reject(
            LPPositionPatchCodeV1.NO_OP_WRITE,
            ("deltas", "net_delta"),
        )
    return None


def _lp_delta_rejection_order_v1(
    reject: LPPositionPatchRejectV1,
) -> tuple[str, tuple[tuple[str, str], ...]]:
    return (
        reject.code.value,
        tuple((type(part).__name__, str(part)) for part in reject.path),
    )


def validate_lp_position_deltas_v1(
    deltas: object,
) -> LPPositionPatchRejectV1 | None:
    """Validate one unordered LP-delta family without reading state."""

    if type(deltas) is not tuple:
        return _lp_reject(LPPositionPatchCodeV1.WRONG_EXACT_TYPE, ("deltas",))
    if len(deltas) > MAX_LP_ENTRIES_V1:
        return _lp_reject(LPPositionPatchCodeV1.ITEM_LIMIT, ("deltas",))

    representation_rejects = tuple(
        reject for delta in deltas if (reject := _lp_delta_reject_v1(delta)) is not None
    )
    if representation_rejects:
        return min(representation_rejects, key=_lp_delta_rejection_order_v1)

    work_bytes = 0
    for delta in cast(tuple[LPPositionDeltaV1, ...], deltas):
        work_bytes += len(delta.key[0].encode("utf-8"))
        work_bytes += len(delta.key[1].encode("utf-8"))
        work_bytes += max(1, (abs(delta.net_delta).bit_length() + 7) // 8)
        if work_bytes > MAX_CANONICAL_BYTES_V1:
            return _lp_reject(LPPositionPatchCodeV1.BYTE_LIMIT, ("deltas",))
    return None


def apply_lp_position_deltas_v1(
    pre: CommittedLPTableV1,
    deltas: tuple[LPPositionDeltaV1, ...],
) -> LPPositionPatchApplyResultV1:
    """Reduce LP balance atoms canonically and return one immutable candidate.

    The exact pre-state is revalidated before work begins. Delta ordering has no
    semantic effect. No mutable ``LPTable`` is constructed, and rejection
    returns no successor value.
    """

    positions = _lp_positions_from_committed_v1(pre)
    if type(positions) is LPPositionPatchRejectV1:
        return positions
    delta_reject = validate_lp_position_deltas_v1(deltas)
    if delta_reject is not None:
        return delta_reject

    aggregate: dict[LPKeyV1, int] = {}
    for delta in deltas:
        aggregate[delta.key] = aggregate.get(delta.key, 0) + delta.net_delta

    writes: list[LPPositionWriteV1] = []
    for key, net_delta in sorted(aggregate.items(), key=lambda item: item[0]):
        if net_delta == 0:
            continue
        current = positions.get(key, _EMPTY_LP_POSITION_V1)
        replacement_balance = current.balance + net_delta
        if not 0 <= replacement_balance <= DEX_LP_AMOUNT_MAX:
            return _lp_reject(
                LPPositionPatchCodeV1.OUT_OF_RANGE,
                ("deltas", "net_delta"),
            )
        replacement = replace(
            current,
            balance=replacement_balance,
            last_mint_timestamp=(current.last_mint_timestamp if replacement_balance > 0 else None),
        )
        writes.append(LPPositionWriteV1(key, current, replacement))

    if not writes:
        return LPPositionPatchApplyOkV1(pre, None)
    patch_result = build_canonical_lp_position_patch_v1(tuple(writes))
    if type(patch_result) is LPPositionPatchRejectV1:
        return patch_result
    return apply_canonical_lp_position_patch_v1(pre, patch_result.patch)


PoolPatchPathPartV1: TypeAlias = str | int
PoolPatchPathV1: TypeAlias = tuple[PoolPatchPathPartV1, ...]


class PoolPatchCodeV1(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    ITEM_LIMIT = "item_limit"
    BYTE_LIMIT = "byte_limit"
    NONCANONICAL_KEY = "noncanonical_key"
    INVALID_POOL_STATE = "invalid_pool_state"
    UNKNOWN_POOL = "unknown_pool"
    ASSET_MISMATCH = "asset_mismatch"
    OUT_OF_RANGE = "out_of_range"
    POOL_ID_MISMATCH = "pool_id_mismatch"
    EMPTY_PATCH = "empty_patch"
    DUPLICATE_WRITE = "duplicate_write"
    NO_OP_WRITE = "no_op_write"
    NONCANONICAL_PATCH = "noncanonical_patch"
    EXPECTED_OLD_MISMATCH = "expected_old_mismatch"
    INVALID_PRESTATE = "invalid_prestate"
    INVALID_CANDIDATE = "invalid_candidate"


@final
@dataclass(frozen=True, slots=True)
class PoolPatchRejectV1:
    """Typed no-output rejection for an internal pool-map patch."""

    code: PoolPatchCodeV1
    path: PoolPatchPathV1


def _pool_reject(code: PoolPatchCodeV1, path: PoolPatchPathV1) -> PoolPatchRejectV1:
    return PoolPatchRejectV1(code, path)


@final
@dataclass(frozen=True, slots=True)
class PoolReserveDeltaV1:
    """One exact additive reserve atom for a named pool asset."""

    pool_id: str
    asset: str
    net_delta: int

    def __post_init__(self) -> None:
        for field_name in ("pool_id", "asset"):
            reject = _pool_key_reject_v1(
                object.__getattribute__(self, field_name),
                (field_name,),
            )
            if reject is not None:
                if reject.code is PoolPatchCodeV1.WRONG_EXACT_TYPE:
                    raise TypeError(f"{field_name} must be an exact string")
                raise ValueError(f"{field_name} is not canonical")
        if type(self.net_delta) is not int:
            raise TypeError("pool reserve net_delta must be an exact integer")
        if self.net_delta == 0:
            raise ValueError("pool reserve net_delta must be nonzero")


@final
@dataclass(frozen=True, slots=True)
class PoolSupplyDeltaV1:
    """One exact additive LP-supply atom for a named pool."""

    pool_id: str
    net_delta: int

    def __post_init__(self) -> None:
        reject = _pool_key_reject_v1(self.pool_id, ("pool_id",))
        if reject is not None:
            if reject.code is PoolPatchCodeV1.WRONG_EXACT_TYPE:
                raise TypeError("pool_id must be an exact string")
            raise ValueError("pool_id is not canonical")
        if type(self.net_delta) is not int:
            raise TypeError("pool supply net_delta must be an exact integer")
        if self.net_delta == 0:
            raise ValueError("pool supply net_delta must be nonzero")


def _pool_key_reject_v1(
    pool_id: object,
    path: PoolPatchPathV1,
) -> PoolPatchRejectV1 | None:
    if type(pool_id) is not str:
        return _pool_reject(PoolPatchCodeV1.WRONG_EXACT_TYPE, path)
    if not pool_id:
        return _pool_reject(PoolPatchCodeV1.NONCANONICAL_KEY, path)
    if len(pool_id) > MAX_STATE_STRING_CHARACTERS_V1:
        return _pool_reject(PoolPatchCodeV1.ITEM_LIMIT, path)
    try:
        encoded = pool_id.encode("utf-8")
    except UnicodeEncodeError:
        return _pool_reject(PoolPatchCodeV1.NONCANONICAL_KEY, path)
    if len(encoded) > MAX_STATE_STRING_UTF8_BYTES_V1:
        return _pool_reject(PoolPatchCodeV1.ITEM_LIMIT, path)
    return None


def _pool_value_shallow_reject_v1(
    value: object,
    pool_id: str,
    path: PoolPatchPathV1,
) -> PoolPatchRejectV1 | None:
    if value is None:
        return None
    if type(value) is not CommittedPoolStateV1:
        return _pool_reject(PoolPatchCodeV1.WRONG_EXACT_TYPE, path)
    try:
        value_pool_id = object.__getattribute__(value, "pool_id")
    except AttributeError:
        return _pool_reject(PoolPatchCodeV1.INVALID_POOL_STATE, path)
    if type(value_pool_id) is not str:
        return _pool_reject(PoolPatchCodeV1.INVALID_POOL_STATE, path + ("pool_id",))
    if value_pool_id != pool_id:
        return _pool_reject(PoolPatchCodeV1.POOL_ID_MISMATCH, path + ("pool_id",))
    return None


@final
@dataclass(frozen=True, slots=True)
class PoolWriteV1:
    """Compare-and-replace one complete exact pool-map cell."""

    pool_id: str
    expected: CommittedPoolStateV1 | None
    replacement: CommittedPoolStateV1 | None

    def __post_init__(self) -> None:
        key_reject = _pool_key_reject_v1(self.pool_id, ("pool_id",))
        if key_reject is not None:
            if key_reject.code is PoolPatchCodeV1.WRONG_EXACT_TYPE:
                raise TypeError("pool patch key must be an exact string")
            raise ValueError("pool patch key is not canonical")
        for field_name in ("expected", "replacement"):
            value_reject = _pool_value_shallow_reject_v1(
                object.__getattribute__(self, field_name),
                self.pool_id,
                (field_name,),
            )
            if value_reject is not None:
                if value_reject.code is PoolPatchCodeV1.WRONG_EXACT_TYPE:
                    raise TypeError(f"{field_name} must be an exact committed pool or None")
                raise ValueError(f"{field_name} does not bind the pool patch key")


def _pool_write_shallow_reject_v1(
    write: object,
    path: PoolPatchPathV1,
) -> PoolPatchRejectV1 | None:
    if type(write) is not PoolWriteV1:
        return _pool_reject(PoolPatchCodeV1.WRONG_EXACT_TYPE, path)
    key_reject = _pool_key_reject_v1(write.pool_id, path + ("pool_id",))
    if key_reject is not None:
        return key_reject
    expected_reject = _pool_value_shallow_reject_v1(
        write.expected,
        write.pool_id,
        path + ("expected",),
    )
    if expected_reject is not None:
        return expected_reject
    return _pool_value_shallow_reject_v1(
        write.replacement,
        write.pool_id,
        path + ("replacement",),
    )


def _pool_value_work_shape_v1(value: CommittedPoolStateV1 | None) -> object:
    if value is None:
        return None
    return (
        value.pool_id,
        value.asset0,
        value.asset1,
        value.reserve0,
        value.reserve1,
        value.fee_bps,
        value.lp_supply,
        (
            value.status.schema_revision,
            value.status.enum_tag_ordinal,
            value.status.member_ordinal,
        ),
        value.created_at,
        value.curve_tag,
        value.curve_params,
    )


def _pool_write_work_bytes_v1(write: PoolWriteV1, remaining: int) -> int | None:
    try:
        return bounded_json_utf8_size(
            (
                write.pool_id,
                _pool_value_work_shape_v1(write.expected),
                _pool_value_work_shape_v1(write.replacement),
            ),
            max_bytes=remaining,
            max_depth=8,
            max_items=64,
        )
    except (TypeError, ValueError):
        return None


def _admit_pool_patch_value_v1(
    value: CommittedPoolStateV1 | None,
    path: PoolPatchPathV1,
) -> CommittedPoolStateV1 | None | PoolPatchRejectV1:
    if value is None:
        return None
    from .state_snapshots import StateAdmissionError, snapshot_pool

    try:
        return snapshot_pool(value)
    except StateAdmissionError as exc:
        return _pool_reject(PoolPatchCodeV1.INVALID_POOL_STATE, path + exc.path)


def _pool_reject_in_mode_v1(
    reject: PoolPatchRejectV1,
    invalid_code: PoolPatchCodeV1 | None,
) -> PoolPatchRejectV1:
    if invalid_code is None:
        return reject
    return _pool_reject(invalid_code, reject.path)


def _sanitize_pool_writes_v1(
    writes: object,
    *,
    invalid_code: PoolPatchCodeV1 | None,
) -> tuple[PoolWriteV1, ...] | PoolPatchRejectV1:
    if type(writes) is not tuple or not writes:
        code = PoolPatchCodeV1.EMPTY_PATCH if invalid_code is None else invalid_code
        return _pool_reject(code, ("writes",))
    if len(writes) > MAX_POOLS_V1:
        return _pool_reject(PoolPatchCodeV1.ITEM_LIMIT, ("writes",))

    admitted_writes: list[PoolWriteV1] = []
    work_bytes = 0
    for index, write in enumerate(writes):
        path: PoolPatchPathV1 = ("writes", index)
        shallow_reject = _pool_write_shallow_reject_v1(write, path)
        if shallow_reject is not None:
            return _pool_reject_in_mode_v1(shallow_reject, invalid_code)
        exact_write = cast(PoolWriteV1, write)
        admitted_expected = _admit_pool_patch_value_v1(
            exact_write.expected,
            path + ("expected",),
        )
        if type(admitted_expected) is PoolPatchRejectV1:
            return _pool_reject_in_mode_v1(admitted_expected, invalid_code)
        admitted_replacement = _admit_pool_patch_value_v1(
            exact_write.replacement,
            path + ("replacement",),
        )
        if type(admitted_replacement) is PoolPatchRejectV1:
            return _pool_reject_in_mode_v1(admitted_replacement, invalid_code)
        admitted_write = PoolWriteV1(
            exact_write.pool_id,
            admitted_expected,
            admitted_replacement,
        )
        write_bytes = _pool_write_work_bytes_v1(
            admitted_write,
            MAX_CANONICAL_BYTES_V1 - work_bytes,
        )
        if write_bytes is None:
            return _pool_reject(PoolPatchCodeV1.BYTE_LIMIT, ("writes",))
        work_bytes += write_bytes
        admitted_writes.append(admitted_write)
    return tuple(admitted_writes)


def _canonical_pool_writes_reject_v1(
    writes: tuple[PoolWriteV1, ...],
    *,
    invalid_code: PoolPatchCodeV1,
) -> PoolPatchRejectV1 | None:
    previous_pool_id: str | None = None
    for index, write in enumerate(writes):
        path: PoolPatchPathV1 = ("writes", index)
        if write.expected == write.replacement:
            return _pool_reject(invalid_code, path)
        if previous_pool_id is not None and previous_pool_id >= write.pool_id:
            return _pool_reject(invalid_code, path + ("pool_id",))
        previous_pool_id = write.pool_id
    return None


@final
@dataclass(frozen=True, slots=True)
class CanonicalPoolPatchV1:
    """Owned sorted pool writes for one internal pure transition.

    Storage commitment is a later ``AtomicCandidate`` contract that binds the
    complete pre-state root, effects, receipt, nonce changes, and outbox.
    """

    writes: tuple[PoolWriteV1, ...]

    def __post_init__(self) -> None:
        admitted = _sanitize_pool_writes_v1(
            self.writes,
            invalid_code=PoolPatchCodeV1.NONCANONICAL_PATCH,
        )
        if type(admitted) is PoolPatchRejectV1:
            raise ValueError("CanonicalPoolPatchV1 requires valid owned writes")
        reject = _canonical_pool_writes_reject_v1(
            admitted,
            invalid_code=PoolPatchCodeV1.NONCANONICAL_PATCH,
        )
        if reject is not None:
            raise ValueError("CanonicalPoolPatchV1 requires canonical writes")


@final
@dataclass(frozen=True, slots=True)
class PoolPatchBuildOkV1:
    patch: CanonicalPoolPatchV1


@final
@dataclass(frozen=True, slots=True)
class PoolPatchApplyOkV1:
    state: OwnedMapV1[str, CommittedPoolStateV1]
    patch: CanonicalPoolPatchV1 | None


PoolPatchBuildResultV1 = PoolPatchBuildOkV1 | PoolPatchRejectV1
PoolPatchApplyResultV1 = PoolPatchApplyOkV1 | PoolPatchRejectV1


def build_canonical_pool_patch_v1(
    writes: tuple[PoolWriteV1, ...],
) -> PoolPatchBuildResultV1:
    """Own and canonically order internal full-pool compare-and-replace writes."""

    admitted = _sanitize_pool_writes_v1(writes, invalid_code=None)
    if type(admitted) is PoolPatchRejectV1:
        return admitted
    canonical = tuple(sorted(admitted, key=lambda write: write.pool_id))
    for index in range(1, len(canonical)):
        if canonical[index - 1].pool_id == canonical[index].pool_id:
            return _pool_reject(
                PoolPatchCodeV1.DUPLICATE_WRITE,
                ("writes", "pool_id", canonical[index].pool_id),
            )
    for index, write in enumerate(canonical):
        if write.expected == write.replacement:
            return _pool_reject(PoolPatchCodeV1.NO_OP_WRITE, ("writes", index))
    return PoolPatchBuildOkV1(CanonicalPoolPatchV1(canonical))


def _validated_pool_patch_writes_v1(
    patch: object,
) -> tuple[PoolWriteV1, ...] | PoolPatchRejectV1:
    if type(patch) is not CanonicalPoolPatchV1:
        return _pool_reject(PoolPatchCodeV1.WRONG_EXACT_TYPE, ())
    try:
        raw_writes = object.__getattribute__(patch, "writes")
    except AttributeError:
        return _pool_reject(PoolPatchCodeV1.NONCANONICAL_PATCH, ("writes",))
    admitted = _sanitize_pool_writes_v1(
        raw_writes,
        invalid_code=PoolPatchCodeV1.NONCANONICAL_PATCH,
    )
    if type(admitted) is PoolPatchRejectV1:
        return admitted
    reject = _canonical_pool_writes_reject_v1(
        admitted,
        invalid_code=PoolPatchCodeV1.NONCANONICAL_PATCH,
    )
    if reject is not None:
        return reject
    return admitted


def _validated_pool_map_v1(
    pre: object,
) -> OwnedMapV1[str, CommittedPoolStateV1] | PoolPatchRejectV1:
    if type(pre) is not OwnedMapV1:
        return _pool_reject(PoolPatchCodeV1.WRONG_EXACT_TYPE, ())
    from .state_snapshots import StateAdmissionError, snapshot_pool_map

    try:
        return snapshot_pool_map(cast(OwnedMapV1[str, CommittedPoolStateV1], pre))
    except StateAdmissionError as exc:
        return _pool_reject(PoolPatchCodeV1.INVALID_PRESTATE, ("state",) + exc.path)


def _pool_candidate_v1(
    values: dict[str, CommittedPoolStateV1],
) -> OwnedMapV1[str, CommittedPoolStateV1] | PoolPatchRejectV1:
    entries = tuple(sorted(values.items(), key=lambda item: item[0]))
    if len(entries) > MAX_POOLS_V1:
        return _pool_reject(PoolPatchCodeV1.ITEM_LIMIT, ("state", "pools"))
    try:
        candidate = _owned_map_from_canonical_transition_v1(
            entries,
            FCIS_STATE_SCHEMA_REVISION_V1,
            POOL_MAP_SCHEMA_ID_V1,
        )
    except (TypeError, ValueError):
        return _pool_reject(PoolPatchCodeV1.INVALID_CANDIDATE, ("state", "pools"))

    from .state_snapshots import StateAdmissionError, snapshot_pool_map

    try:
        return snapshot_pool_map(candidate)
    except StateAdmissionError as exc:
        return _pool_reject(PoolPatchCodeV1.INVALID_CANDIDATE, ("state",) + exc.path)


def apply_canonical_pool_patch_v1(
    pre: OwnedMapV1[str, CommittedPoolStateV1],
    patch: CanonicalPoolPatchV1,
) -> PoolPatchApplyResultV1:
    """Apply a full-pool patch atomically over one exact immutable pool map."""

    admitted_pre = _validated_pool_map_v1(pre)
    if type(admitted_pre) is PoolPatchRejectV1:
        return admitted_pre
    writes = _validated_pool_patch_writes_v1(patch)
    if type(writes) is PoolPatchRejectV1:
        return writes

    updated = dict(admitted_pre.entries)
    for index, write in enumerate(writes):
        current = updated.get(write.pool_id)
        if current != write.expected:
            return _pool_reject(
                PoolPatchCodeV1.EXPECTED_OLD_MISMATCH,
                ("writes", index, "expected"),
            )
        if write.replacement is None:
            updated.pop(write.pool_id, None)
        else:
            updated[write.pool_id] = write.replacement

    candidate = _pool_candidate_v1(updated)
    if type(candidate) is PoolPatchRejectV1:
        return candidate
    return PoolPatchApplyOkV1(candidate, patch)


def _pool_reserve_delta_reject_v1(delta: object) -> PoolPatchRejectV1 | None:
    if type(delta) is not PoolReserveDeltaV1:
        return _pool_reject(PoolPatchCodeV1.WRONG_EXACT_TYPE, ("reserve_deltas",))
    for field_name in ("pool_id", "asset"):
        reject = _pool_key_reject_v1(
            object.__getattribute__(delta, field_name),
            ("reserve_deltas", field_name),
        )
        if reject is not None:
            return reject
    if type(delta.net_delta) is not int:
        return _pool_reject(
            PoolPatchCodeV1.WRONG_EXACT_TYPE,
            ("reserve_deltas", "net_delta"),
        )
    if delta.net_delta == 0:
        return _pool_reject(
            PoolPatchCodeV1.NO_OP_WRITE,
            ("reserve_deltas", "net_delta"),
        )
    return None


def _pool_supply_delta_reject_v1(delta: object) -> PoolPatchRejectV1 | None:
    if type(delta) is not PoolSupplyDeltaV1:
        return _pool_reject(PoolPatchCodeV1.WRONG_EXACT_TYPE, ("supply_deltas",))
    reject = _pool_key_reject_v1(delta.pool_id, ("supply_deltas", "pool_id"))
    if reject is not None:
        return reject
    if type(delta.net_delta) is not int:
        return _pool_reject(
            PoolPatchCodeV1.WRONG_EXACT_TYPE,
            ("supply_deltas", "net_delta"),
        )
    if delta.net_delta == 0:
        return _pool_reject(
            PoolPatchCodeV1.NO_OP_WRITE,
            ("supply_deltas", "net_delta"),
        )
    return None


def _pool_delta_rejection_order_v1(
    reject: PoolPatchRejectV1,
) -> tuple[str, tuple[tuple[str, str], ...]]:
    return (
        reject.code.value,
        tuple((type(part).__name__, str(part)) for part in reject.path),
    )


def _pool_delta_work_bytes_v1(*values: object) -> int:
    total = 0
    for value in values:
        if type(value) is str:
            total += len(value.encode("utf-8"))
        elif type(value) is int:
            total += max(1, (abs(value).bit_length() + 7) // 8)
    return total


@dataclass(frozen=True, slots=True)
class _PoolDeltaNetsV1:
    reserve_entries: tuple[tuple[tuple[str, str], int], ...]
    supply_entries: tuple[tuple[str, int], ...]


def _aggregate_pool_deltas_v1(
    reserve_deltas: tuple[PoolReserveDeltaV1, ...],
    supply_deltas: tuple[PoolSupplyDeltaV1, ...],
) -> _PoolDeltaNetsV1 | PoolPatchRejectV1:
    if type(reserve_deltas) is not tuple:
        return _pool_reject(PoolPatchCodeV1.WRONG_EXACT_TYPE, ("reserve_deltas",))
    if type(supply_deltas) is not tuple:
        return _pool_reject(PoolPatchCodeV1.WRONG_EXACT_TYPE, ("supply_deltas",))
    if len(reserve_deltas) + len(supply_deltas) > MAX_COLLECTION_ITEMS_V1:
        return _pool_reject(PoolPatchCodeV1.ITEM_LIMIT, ("deltas",))

    representation_rejects = tuple(
        reject
        for delta in reserve_deltas
        if (reject := _pool_reserve_delta_reject_v1(delta)) is not None
    ) + tuple(
        reject
        for delta in supply_deltas
        if (reject := _pool_supply_delta_reject_v1(delta)) is not None
    )
    if representation_rejects:
        return min(representation_rejects, key=_pool_delta_rejection_order_v1)

    reserve_net: dict[tuple[str, str], int] = {}
    supply_net: dict[str, int] = {}
    work_bytes = 0
    for reserve_delta in reserve_deltas:
        work_bytes += _pool_delta_work_bytes_v1(
            reserve_delta.pool_id,
            reserve_delta.asset,
            reserve_delta.net_delta,
        )
        if work_bytes > MAX_CANONICAL_BYTES_V1:
            return _pool_reject(PoolPatchCodeV1.BYTE_LIMIT, ("reserve_deltas",))
        key = (reserve_delta.pool_id, reserve_delta.asset)
        reserve_net[key] = reserve_net.get(key, 0) + reserve_delta.net_delta
    for supply_delta in supply_deltas:
        work_bytes += _pool_delta_work_bytes_v1(
            supply_delta.pool_id,
            supply_delta.net_delta,
        )
        if work_bytes > MAX_CANONICAL_BYTES_V1:
            return _pool_reject(PoolPatchCodeV1.BYTE_LIMIT, ("supply_deltas",))
        supply_net[supply_delta.pool_id] = (
            supply_net.get(supply_delta.pool_id, 0) + supply_delta.net_delta
        )

    return _PoolDeltaNetsV1(
        tuple(sorted(reserve_net.items(), key=lambda item: item[0])),
        tuple(sorted(supply_net.items(), key=lambda item: item[0])),
    )


def validate_pool_deltas_v1(
    reserve_deltas: object,
    supply_deltas: object,
) -> PoolPatchRejectV1 | None:
    """Validate unordered pool-delta families without reading pool state."""

    nets = _aggregate_pool_deltas_v1(
        cast(tuple[PoolReserveDeltaV1, ...], reserve_deltas),
        cast(tuple[PoolSupplyDeltaV1, ...], supply_deltas),
    )
    if type(nets) is PoolPatchRejectV1:
        return nets
    return None


def _pool_delta_replacement_v1(
    current: CommittedPoolStateV1,
    reserve_entries: tuple[tuple[str, int], ...],
    supply_net: int,
) -> CommittedPoolStateV1 | PoolPatchRejectV1:
    reserve0 = current.reserve0
    reserve1 = current.reserve1
    for asset, net_delta in reserve_entries:
        if asset == current.asset0:
            reserve0 += net_delta
        elif asset == current.asset1:
            reserve1 += net_delta
        else:
            return _pool_reject(
                PoolPatchCodeV1.ASSET_MISMATCH,
                ("pools", current.pool_id, "asset"),
            )
    lp_supply = current.lp_supply + supply_net
    if not (
        0 <= reserve0 <= DEX_POOL_RESERVE_MAX
        and 0 <= reserve1 <= DEX_POOL_RESERVE_MAX
        and 0 <= lp_supply <= DEX_LP_SUPPLY_MAX
    ):
        return _pool_reject(
            PoolPatchCodeV1.OUT_OF_RANGE,
            ("pools", current.pool_id),
        )
    try:
        return replace(
            current,
            reserve0=reserve0,
            reserve1=reserve1,
            lp_supply=lp_supply,
        )
    except (TypeError, ValueError):
        return _pool_reject(
            PoolPatchCodeV1.INVALID_POOL_STATE,
            ("pools", current.pool_id),
        )


def _pool_delta_writes_v1(
    pre: OwnedMapV1[str, CommittedPoolStateV1],
    nets: _PoolDeltaNetsV1,
) -> tuple[PoolWriteV1, ...] | PoolPatchRejectV1:
    reserve_by_pool: dict[str, list[tuple[str, int]]] = {}
    for (pool_id, asset), net_delta in nets.reserve_entries:
        reserve_by_pool.setdefault(pool_id, []).append((asset, net_delta))
    supply_by_pool = dict(nets.supply_entries)
    touched_pool_ids = sorted(set(reserve_by_pool) | set(supply_by_pool))

    writes: list[PoolWriteV1] = []
    for pool_id in touched_pool_ids:
        current = pre.get(pool_id)
        if current is None:
            return _pool_reject(
                PoolPatchCodeV1.UNKNOWN_POOL,
                ("pools", pool_id),
            )
        replacement = _pool_delta_replacement_v1(
            current,
            tuple(reserve_by_pool.get(pool_id, ())),
            supply_by_pool.get(pool_id, 0),
        )
        if type(replacement) is PoolPatchRejectV1:
            return replacement
        if replacement == current:
            continue
        writes.append(PoolWriteV1(pool_id, current, replacement))
    return tuple(writes)


def apply_pool_deltas_v1(
    pre: OwnedMapV1[str, CommittedPoolStateV1],
    reserve_deltas: tuple[PoolReserveDeltaV1, ...],
    supply_deltas: tuple[PoolSupplyDeltaV1, ...],
) -> PoolPatchApplyResultV1:
    """Reduce reserve and LP-supply atoms into complete immutable pool writes."""

    admitted_pre = _validated_pool_map_v1(pre)
    if type(admitted_pre) is PoolPatchRejectV1:
        return admitted_pre
    nets = _aggregate_pool_deltas_v1(reserve_deltas, supply_deltas)
    if type(nets) is PoolPatchRejectV1:
        return nets
    writes = _pool_delta_writes_v1(admitted_pre, nets)
    if type(writes) is PoolPatchRejectV1:
        return writes

    if not writes:
        return PoolPatchApplyOkV1(admitted_pre, None)
    patch_result = build_canonical_pool_patch_v1(writes)
    if type(patch_result) is PoolPatchRejectV1:
        return patch_result
    return apply_canonical_pool_patch_v1(admitted_pre, patch_result.patch)


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
    "CanonicalLPPositionPatchV1",
    "CanonicalNoncePatchV1",
    "CanonicalPoolPatchV1",
    "LPPositionDeltaV1",
    "LPPositionPatchApplyOkV1",
    "LPPositionPatchApplyResultV1",
    "LPPositionPatchBuildOkV1",
    "LPPositionPatchBuildResultV1",
    "LPPositionPatchCodeV1",
    "LPPositionPatchRejectV1",
    "LPPositionValueV1",
    "LPPositionWriteV1",
    "NonceAdvanceV1",
    "NoncePatchApplyOkV1",
    "NoncePatchApplyResultV1",
    "NoncePatchBuildOkV1",
    "NoncePatchBuildResultV1",
    "NoncePatchCodeV1",
    "NoncePatchRejectV1",
    "PoolPatchApplyOkV1",
    "PoolPatchApplyResultV1",
    "PoolPatchBuildOkV1",
    "PoolPatchBuildResultV1",
    "PoolPatchCodeV1",
    "PoolPatchRejectV1",
    "PoolReserveDeltaV1",
    "PoolSupplyDeltaV1",
    "PoolWriteV1",
    "apply_balance_deltas_v1",
    "apply_canonical_balance_patch_v1",
    "apply_canonical_lp_position_patch_v1",
    "apply_canonical_nonce_patch_v1",
    "apply_canonical_pool_patch_v1",
    "apply_lp_position_deltas_v1",
    "apply_pool_deltas_v1",
    "build_canonical_balance_patch_v1",
    "build_canonical_lp_position_patch_v1",
    "build_canonical_nonce_patch_v1",
    "build_canonical_pool_patch_v1",
    "validate_balance_deltas_v1",
    "validate_committed_balance_state_v1",
    "validate_committed_nonce_state_v1",
    "validate_lp_position_deltas_v1",
    "validate_pool_deltas_v1",
]
