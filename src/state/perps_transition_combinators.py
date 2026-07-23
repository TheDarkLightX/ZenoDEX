"""Closed deterministic patch combinators for isolated-perps transitions.

These helpers join exact immutable entry tuples and return only exact immutable
tuples, canonical patches, or stable no-output rejection values. The join path
does not allocate or expose a mutable work buffer.
"""

from __future__ import annotations

from bisect import bisect_left
from typing import TypeAlias, cast

from ..core.perps import PERP_ISOLATED_GLOBAL_KEYS
from .perps_account_transitions import (
    CanonicalIsolatedAccountPatchV1,
    IsolatedAccountWriteV1,
    _canonical_pubkey_reject,
)
from .perps_state_transitions import (
    CanonicalIsolatedGlobalPatchV1,
    IsolatedGlobalWriteV1,
    IsolatedPerpTransitionCodeV1,
    IsolatedPerpTransitionRejectV1,
    _is_exact_perps_value,
)
from .state_snapshot_values import (
    CommittedPerpAccountStateV1,
    CommittedPerpMarketStateV1,
    PerpsValueV1,
)

FCIS_MUTABLE_LOCAL_BUFFERS_FORBIDDEN = True

_AccountEntriesV1: TypeAlias = tuple[
    tuple[str, CommittedPerpAccountStateV1],
    ...,
]
_AccountPatchAndEntriesV1: TypeAlias = tuple[
    CanonicalIsolatedAccountPatchV1 | None,
    _AccountEntriesV1,
]
_GLOBAL_FIELD_ORDER_V1 = tuple(sorted(PERP_ISOLATED_GLOBAL_KEYS))


def _reject(
    code: IsolatedPerpTransitionCodeV1,
    path: tuple[str | int, ...],
) -> IsolatedPerpTransitionRejectV1:
    return IsolatedPerpTransitionRejectV1(code, path)


def _first_isolated_reject(
    values: tuple[object, ...],
) -> IsolatedPerpTransitionRejectV1 | None:
    """Select the first rejection from an already canonical immutable sequence."""

    return next(
        (value for value in values if type(value) is IsolatedPerpTransitionRejectV1),
        None,
    )


def _replacement_or_expected(
    replacement_keys: tuple[str, ...],
    replacements: _AccountEntriesV1,
    account_pubkey: str,
    expected: CommittedPerpAccountStateV1,
) -> CommittedPerpAccountStateV1:
    replacement_index = bisect_left(replacement_keys, account_pubkey)
    if (
        replacement_index < len(replacement_keys)
        and replacement_keys[replacement_index] == account_pubkey
    ):
        return replacements[replacement_index][1]
    return expected


def _existing_account_patch_and_entries(
    pre: CommittedPerpMarketStateV1,
    replacements: object,
) -> _AccountPatchAndEntriesV1 | IsolatedPerpTransitionRejectV1:
    """Join sorted replacements with the same committed account snapshot."""

    validated = _validated_existing_account_replacements(replacements)
    if type(validated) is IsolatedPerpTransitionRejectV1:
        return validated
    replacement_keys = tuple(account_pubkey for account_pubkey, _value in validated)
    missing_pubkey = next(
        (
            account_pubkey
            for account_pubkey in replacement_keys
            if pre.get_account(account_pubkey) is None
        ),
        None,
    )
    if missing_pubkey is not None:
        return _reject(
            IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE,
            ("state", "accounts", missing_pubkey),
        )
    candidate_entries = tuple(
        (
            account_pubkey,
            _replacement_or_expected(
                replacement_keys,
                validated,
                account_pubkey,
                expected,
            ),
        )
        for account_pubkey, expected in pre.account_entries
    )
    try:
        writes = tuple(
            IsolatedAccountWriteV1(account_pubkey, expected, replacement)
            for (account_pubkey, expected), (_candidate_key, replacement) in zip(
                pre.account_entries,
                candidate_entries,
                strict=True,
            )
            if expected != replacement
        )
    except (TypeError, ValueError):
        return _reject(
            IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE,
            ("patch", "accounts"),
        )
    if not writes:
        return None, pre.account_entries
    try:
        patch = CanonicalIsolatedAccountPatchV1(writes)
    except (TypeError, ValueError):
        return _reject(
            IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE,
            ("patch", "accounts"),
        )
    return patch, tuple(candidate_entries)


def _validated_existing_account_replacements(
    replacements: object,
) -> _AccountEntriesV1 | IsolatedPerpTransitionRejectV1:
    if type(replacements) is not tuple:
        return _reject(
            IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE,
            ("state", "accounts"),
        )
    previous_key: str | None = None
    for index, entry in enumerate(replacements):
        path = ("state", "accounts", index)
        if type(entry) is not tuple or len(entry) != 2:
            return _reject(IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE, path)
        account_pubkey, replacement = entry
        key_reject = _canonical_pubkey_reject(
            account_pubkey,
            path + ("account_pubkey",),
        )
        if key_reject is not None or type(replacement) is not CommittedPerpAccountStateV1:
            return _reject(IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE, path)
        exact_key = cast(str, account_pubkey)
        if previous_key is not None and previous_key >= exact_key:
            return _reject(IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE, path)
        previous_key = exact_key
    return cast(_AccountEntriesV1, replacements)


def _build_optional_global_patch_from_entries(
    before: object,
    after: object,
) -> CanonicalIsolatedGlobalPatchV1 | IsolatedPerpTransitionRejectV1 | None:
    """Build one canonical global patch from immutable entry tuples."""

    if type(before) is not tuple or type(after) is not tuple:
        return _reject(
            IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE,
            ("patch", "global"),
        )
    before_entries = cast(tuple[object, ...], before)
    after_entries = cast(tuple[object, ...], after)
    if len(before_entries) != len(after_entries) or len(before_entries) != len(
        _GLOBAL_FIELD_ORDER_V1
    ):
        return _reject(
            IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE,
            ("patch", "global"),
        )

    pair_results = tuple(
        _validated_global_entry_pair(
            before_entry,
            after_entry,
            index=index,
            expected_field=_GLOBAL_FIELD_ORDER_V1[index],
        )
        for index, (before_entry, after_entry) in enumerate(
            zip(before_entries, after_entries, strict=True)
        )
    )
    first_reject = _first_isolated_reject(cast(tuple[object, ...], pair_results))
    if first_reject is not None:
        return first_reject
    exact_pairs = cast(
        tuple[tuple[str, PerpsValueV1, PerpsValueV1], ...],
        pair_results,
    )
    try:
        writes = tuple(
            IsolatedGlobalWriteV1(before_field, before_value, after_value)
            for before_field, before_value, after_value in exact_pairs
            if type(before_value) is not type(after_value) or before_value != after_value
        )
    except (TypeError, ValueError):
        return _reject(
            IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE,
            ("patch", "global"),
        )
    if not writes:
        return None
    try:
        return CanonicalIsolatedGlobalPatchV1(writes)
    except (TypeError, ValueError):
        return _reject(
            IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE,
            ("patch", "global"),
        )


def _validated_global_entry_pair(
    before_entry: object,
    after_entry: object,
    *,
    index: int,
    expected_field: str,
) -> tuple[str, PerpsValueV1, PerpsValueV1] | IsolatedPerpTransitionRejectV1:
    path = ("patch", "global", index)
    if (
        type(before_entry) is not tuple
        or len(before_entry) != 2
        or type(after_entry) is not tuple
        or len(after_entry) != 2
    ):
        return _reject(IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE, path)
    before_field, before_value = before_entry
    after_field, after_value = after_entry
    if (
        type(before_field) is not str
        or type(after_field) is not str
        or before_field != expected_field
        or before_field != after_field
        or not _is_exact_perps_value(before_value)
        or not _is_exact_perps_value(after_value)
    ):
        return _reject(IsolatedPerpTransitionCodeV1.INVALID_CANDIDATE, path)
    return (
        before_field,
        cast(PerpsValueV1, before_value),
        cast(PerpsValueV1, after_value),
    )
