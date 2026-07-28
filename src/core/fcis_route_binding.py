"""Exact route binding derivation and replay for the FCIS M5-P4B3 route path.

Structural shape is admitted solely by the closed snapshot combinator through
``INTENT_SCHEMA_V1``.  This module performs the ordered cross-field derivation
over the admitted values, then replays only a verified ``RouteBindingV1``
against an exact committed pool map.  Replay recursively revalidates the
binding and every nested child before reading any pool, so hostile in-process
corruption returns the closed invalid-binding rejection with no pool read and
no partial replay value.
"""

from __future__ import annotations

from dataclasses import dataclass
from types import MappingProxyType
from typing import cast, final

from typing_extensions import TypeIs

from ..state.fcis_route_binding_schema import (
    ROUTE_LEG_SCHEMA_ID_V1,
    ROUTE_LEGS_MAX_V1,
    ROUTE_POOL_FINGERPRINTS_MAX_V1,
    ROUTE_POOL_FINGERPRINTS_SCHEMA_ID_V1,
)
from ..state.intent_snapshots import (
    OwnedIntentV1,
    owned_intent_field_v1,
    owned_intent_kind_text_v1,
)
from ..state.intents import IntentKind
from ..state.owned_collections import OwnedMapV1
from ..state.state_snapshot_values import (
    FCIS_STATE_SCHEMA_REVISION_V1,
    POOL_MAP_SCHEMA_ID_V1,
    POOL_STATUS_ACTIVE_MEMBER_ORDINAL_V1,
    CommittedPoolStateV1,
)
from .amm_dispatch import (
    swap_exact_in_for_committed_pool_v1,
    swap_exact_out_for_committed_pool_v1,
)
from .cpmm import compute_fee_total
from .domain_limits import DEX_SWAP_AMOUNT_MAX
from .fcis_route_binding_values import (
    _ROUTE_BINDING_CONSTRUCTION_TOKEN_V1,
    RouteBindingOkV1,
    RouteBindingRejectCodeV1,
    RouteBindingRejectV1,
    RouteBindingResultV1,
    RouteBindingV1,
    RouteKindV1,
    RouteLegBindingV1,
    RouteReplayLegV1,
    RouteReplayOkV1,
    RouteReplayRejectCodeV1,
    RouteReplayRejectV1,
    RouteReplayResultV1,
)
from .quote_receipts import pool_state_fingerprint_committed_v1

_ROUTE_SUM_MAX_V1 = ROUTE_LEGS_MAX_V1 * DEX_SWAP_AMOUNT_MAX
_LEG_ENTRY_NAMES_V1 = ("amount_in", "amount_out", "asset_in", "asset_out", "pool_id")


@final
@dataclass(frozen=True, slots=True)
class _RouteLegFieldsV1:
    pool_id: str
    asset_in: str
    asset_out: str
    amount_in: int
    amount_out: int


@final
@dataclass(frozen=True, slots=True)
class _RouteFieldsV1:
    asset_in: str
    asset_out: str
    leg_indices: tuple[int, ...]
    legs: tuple[_RouteLegFieldsV1, ...]
    pool_fingerprints: OwnedMapV1[str, str]
    signed_amount: int
    limit_amount: int


def _binding_reject_v1(
    code: RouteBindingRejectCodeV1,
    path: tuple[str | int, ...],
) -> RouteBindingRejectV1:
    return RouteBindingRejectV1(code, path, _ROUTE_BINDING_CONSTRUCTION_TOKEN_V1)


def _replay_reject_v1(code: RouteReplayRejectCodeV1) -> RouteReplayRejectV1:
    return RouteReplayRejectV1(code, _ROUTE_BINDING_CONSTRUCTION_TOKEN_V1)


def _is_binding_reject_v1(value: object) -> TypeIs[RouteBindingRejectV1]:
    return type(value) is RouteBindingRejectV1


def _is_replay_reject_code_v1(
    value: RouteReplayLegV1 | RouteReplayRejectCodeV1,
) -> TypeIs[RouteReplayRejectCodeV1]:
    return type(value) is RouteReplayRejectCodeV1


def _is_route_text_v1(value: object) -> bool:
    return type(value) is str and 0 < len(value) <= 256 and len(value.encode("utf-8")) <= 1_024


def _is_route_hash_v1(value: object) -> bool:
    return (
        type(value) is str
        and len(value) == 66
        and value[:2] == "0x"
        and all(character in "0123456789abcdef" for character in value[2:])
    )


def _is_route_amount_v1(value: object, minimum: int) -> bool:
    return type(value) is int and minimum <= value <= DEX_SWAP_AMOUNT_MAX


def _owned_map_index_is_consistent_v1(owned: OwnedMapV1[object, object]) -> bool:
    try:
        entries = object.__getattribute__(owned, "_entries")
        index = object.__getattribute__(owned, "_index")
        if type(entries) is not tuple or type(index) is not type(MappingProxyType({})):
            return False
        if len(index) != len(entries):
            return False
        missing = object()
        for entry in entries:
            if type(entry) is not tuple or len(entry) != 2:
                return False
            key, value = entry
            if index.get(key, missing) is not value:
                return False
        return True
    except (AttributeError, TypeError):
        return False


def _fingerprints_are_exact_v1(fingerprints: OwnedMapV1[str, str]) -> bool:
    try:
        entries = object.__getattribute__(fingerprints, "_entries")
    except AttributeError:
        return False
    if type(entries) is not tuple or not 1 <= len(entries) <= ROUTE_POOL_FINGERPRINTS_MAX_V1:
        return False
    if any(type(entry) is not tuple or len(entry) != 2 for entry in entries):
        return False
    if any(not _is_route_text_v1(key) or not _is_route_hash_v1(value) for key, value in entries):
        return False
    if entries != tuple(sorted(entries, key=lambda entry: entry[0])):
        return False
    if len({key for key, _value in entries}) != len(entries):
        return False
    return _owned_map_index_is_consistent_v1(fingerprints)


def _route_kind_of_v1(intent: OwnedIntentV1) -> RouteKindV1 | None:
    kind_text = owned_intent_kind_text_v1(intent)
    if kind_text == IntentKind.ROUTE_EXACT_IN.value:
        return RouteKindV1.EXACT_IN
    if kind_text == IntentKind.ROUTE_EXACT_OUT.value:
        return RouteKindV1.EXACT_OUT
    return None


def _structural_text_field_v1(
    intent: OwnedIntentV1,
    name: str,
) -> str | RouteBindingRejectV1:
    value = owned_intent_field_v1(intent, name, None)
    if not _is_route_text_v1(value):
        return _binding_reject_v1(RouteBindingRejectCodeV1.STRUCTURAL_INVALID, (name,))
    return cast(str, value)


def _structural_amount_field_v1(
    intent: OwnedIntentV1,
    name: str,
    minimum: int,
) -> int | RouteBindingRejectV1:
    value = owned_intent_field_v1(intent, name, None)
    if not _is_route_amount_v1(value, minimum):
        return _binding_reject_v1(RouteBindingRejectCodeV1.STRUCTURAL_INVALID, (name,))
    return cast(int, value)


def _structural_leg_indices_v1(intent: OwnedIntentV1) -> tuple[int, ...] | RouteBindingRejectV1:
    path = ("leg_indices",)
    value = owned_intent_field_v1(intent, "leg_indices", None)
    if type(value) is not tuple or not 1 <= len(value) <= ROUTE_LEGS_MAX_V1:
        return _binding_reject_v1(RouteBindingRejectCodeV1.STRUCTURAL_INVALID, path)
    indices = cast(tuple[object, ...], value)
    if any(type(index) is not int or index < 0 for index in indices):
        return _binding_reject_v1(RouteBindingRejectCodeV1.STRUCTURAL_INVALID, path)
    return cast(tuple[int, ...], value)


def _structural_leg_v1(
    raw_leg: object,
    path: tuple[str | int, ...],
) -> _RouteLegFieldsV1 | RouteBindingRejectV1:
    reject = _binding_reject_v1(RouteBindingRejectCodeV1.STRUCTURAL_INVALID, path)
    if type(raw_leg) is not OwnedMapV1:
        return reject
    leg = cast(OwnedMapV1[str, object], raw_leg)
    if not _owned_map_index_is_consistent_v1(leg):
        return reject
    if (
        leg.schema_revision != FCIS_STATE_SCHEMA_REVISION_V1
        or leg.schema_id != ROUTE_LEG_SCHEMA_ID_V1
    ):
        return reject
    entries = leg.entries
    if tuple(name for name, _value in entries) != _LEG_ENTRY_NAMES_V1:
        return reject
    amount_in = entries[0][1]
    amount_out = entries[1][1]
    asset_in = entries[2][1]
    asset_out = entries[3][1]
    pool_id = entries[4][1]
    if not (_is_route_amount_v1(amount_in, 1) and _is_route_amount_v1(amount_out, 1)):
        return reject
    if not (
        _is_route_text_v1(asset_in) and _is_route_text_v1(asset_out) and _is_route_text_v1(pool_id)
    ):
        return reject
    return _RouteLegFieldsV1(
        cast(str, pool_id),
        cast(str, asset_in),
        cast(str, asset_out),
        cast(int, amount_in),
        cast(int, amount_out),
    )


def _structural_legs_v1(
    intent: OwnedIntentV1,
) -> tuple[_RouteLegFieldsV1, ...] | RouteBindingRejectV1:
    path = ("route_legs",)
    value = owned_intent_field_v1(intent, "route_legs", None)
    if type(value) is not tuple or not 1 <= len(value) <= ROUTE_LEGS_MAX_V1:
        return _binding_reject_v1(RouteBindingRejectCodeV1.STRUCTURAL_INVALID, path)
    legs: list[_RouteLegFieldsV1] = []
    for index, raw_leg in enumerate(cast(tuple[object, ...], value)):
        leg = _structural_leg_v1(raw_leg, ("route_legs", index))
        if _is_binding_reject_v1(leg):
            return leg
        legs.append(leg)
    return tuple(legs)


def _structural_fingerprints_v1(
    intent: OwnedIntentV1,
) -> OwnedMapV1[str, str] | RouteBindingRejectV1:
    path = ("route_pool_fingerprints",)
    value = owned_intent_field_v1(intent, "route_pool_fingerprints", None)
    if type(value) is not OwnedMapV1:
        return _binding_reject_v1(RouteBindingRejectCodeV1.STRUCTURAL_INVALID, path)
    fingerprints = cast(OwnedMapV1[str, str], value)
    if (
        fingerprints.schema_revision != FCIS_STATE_SCHEMA_REVISION_V1
        or fingerprints.schema_id != ROUTE_POOL_FINGERPRINTS_SCHEMA_ID_V1
        or not _fingerprints_are_exact_v1(fingerprints)
    ):
        return _binding_reject_v1(RouteBindingRejectCodeV1.STRUCTURAL_INVALID, path)
    return fingerprints


def _structural_totals_v1(
    intent: OwnedIntentV1,
    kind: RouteKindV1,
) -> tuple[int, int] | RouteBindingRejectV1:
    if kind is RouteKindV1.EXACT_IN:
        names = ("total_amount_in", "total_min_amount_out")
        minimums = (1, 0)
    else:
        names = ("total_amount_out", "total_max_amount_in")
        minimums = (1, 0)
    signed = _structural_amount_field_v1(intent, names[0], minimums[0])
    if _is_binding_reject_v1(signed):
        return signed
    limit = _structural_amount_field_v1(intent, names[1], minimums[1])
    if _is_binding_reject_v1(limit):
        return limit
    return signed, limit


def _read_route_fields_v1(
    intent: OwnedIntentV1,
    kind: RouteKindV1,
) -> _RouteFieldsV1 | RouteBindingRejectV1:
    asset_in = _structural_text_field_v1(intent, "asset_in")
    if _is_binding_reject_v1(asset_in):
        return asset_in
    asset_out = _structural_text_field_v1(intent, "asset_out")
    if _is_binding_reject_v1(asset_out):
        return asset_out
    leg_indices = _structural_leg_indices_v1(intent)
    if _is_binding_reject_v1(leg_indices):
        return leg_indices
    legs = _structural_legs_v1(intent)
    if _is_binding_reject_v1(legs):
        return legs
    fingerprints = _structural_fingerprints_v1(intent)
    if _is_binding_reject_v1(fingerprints):
        return fingerprints
    totals = _structural_totals_v1(intent, kind)
    if _is_binding_reject_v1(totals):
        return totals
    return _RouteFieldsV1(
        asset_in,
        asset_out,
        leg_indices,
        legs,
        fingerprints,
        totals[0],
        totals[1],
    )


def _check_distinct_endpoints_v1(fields: _RouteFieldsV1) -> RouteBindingRejectV1 | None:
    if fields.asset_in == fields.asset_out:
        return _binding_reject_v1(RouteBindingRejectCodeV1.ENDPOINT_ASSETS_INVALID, ("asset_out",))
    return None


def _check_leg_coverage_v1(fields: _RouteFieldsV1) -> RouteBindingRejectV1 | None:
    if fields.leg_indices != tuple(range(len(fields.legs))):
        return _binding_reject_v1(RouteBindingRejectCodeV1.LEG_COVERAGE_MISMATCH, ("leg_indices",))
    return None


def _check_leg_endpoints_v1(fields: _RouteFieldsV1) -> RouteBindingRejectV1 | None:
    for index, leg in enumerate(fields.legs):
        if leg.asset_in != fields.asset_in or leg.asset_out != fields.asset_out:
            return _binding_reject_v1(
                RouteBindingRejectCodeV1.LEG_ENDPOINT_MISMATCH,
                ("route_legs", index),
            )
    return None


def _check_fingerprint_pool_coverage_v1(fields: _RouteFieldsV1) -> RouteBindingRejectV1 | None:
    leg_pool_ids = tuple(sorted({leg.pool_id for leg in fields.legs}))
    fingerprint_pool_ids = tuple(key for key, _value in fields.pool_fingerprints.entries)
    if leg_pool_ids != fingerprint_pool_ids:
        return _binding_reject_v1(
            RouteBindingRejectCodeV1.FINGERPRINT_POOL_MISMATCH,
            ("route_pool_fingerprints",),
        )
    return None


def _bounded_leg_amount_sums_v1(
    legs: tuple[_RouteLegFieldsV1, ...] | tuple[RouteLegBindingV1, ...],
) -> tuple[int, int] | None:
    sum_in = 0
    sum_out = 0
    for leg in legs:
        sum_in += leg.amount_in
        sum_out += leg.amount_out
        if sum_in > _ROUTE_SUM_MAX_V1 or sum_out > _ROUTE_SUM_MAX_V1:
            return None
    return sum_in, sum_out


def _check_kind_totals_v1(
    kind: RouteKindV1,
    fields: _RouteFieldsV1,
    sum_in: int,
    sum_out: int,
) -> RouteBindingRejectV1 | None:
    if kind is RouteKindV1.EXACT_IN:
        if fields.signed_amount != sum_in:
            return _binding_reject_v1(
                RouteBindingRejectCodeV1.EXACT_IN_TOTALS_MISMATCH,
                ("total_amount_in",),
            )
        if fields.limit_amount > sum_out:
            return _binding_reject_v1(
                RouteBindingRejectCodeV1.EXACT_IN_TOTALS_MISMATCH,
                ("total_min_amount_out",),
            )
        return None
    if fields.signed_amount != sum_out:
        return _binding_reject_v1(
            RouteBindingRejectCodeV1.EXACT_OUT_TOTALS_MISMATCH,
            ("total_amount_out",),
        )
    if fields.limit_amount < sum_in:
        return _binding_reject_v1(
            RouteBindingRejectCodeV1.EXACT_OUT_TOTALS_MISMATCH,
            ("total_max_amount_in",),
        )
    return None


def _construct_exact_binding_v1(
    kind: RouteKindV1,
    fields: _RouteFieldsV1,
    sum_in: int,
    sum_out: int,
) -> RouteBindingOkV1:
    legs = tuple(
        RouteLegBindingV1(
            leg.pool_id,
            leg.asset_in,
            leg.asset_out,
            leg.amount_in,
            leg.amount_out,
            _ROUTE_BINDING_CONSTRUCTION_TOKEN_V1,
        )
        for leg in fields.legs
    )
    binding = RouteBindingV1(
        kind,
        fields.asset_in,
        fields.asset_out,
        sum_in,
        sum_out,
        legs,
        fields.pool_fingerprints,
        _ROUTE_BINDING_CONSTRUCTION_TOKEN_V1,
    )
    return RouteBindingOkV1(binding, _ROUTE_BINDING_CONSTRUCTION_TOKEN_V1)


def _derive_cross_field_binding_v1(
    kind: RouteKindV1,
    fields: _RouteFieldsV1,
) -> RouteBindingResultV1:
    for check in (
        _check_distinct_endpoints_v1,
        _check_leg_coverage_v1,
        _check_leg_endpoints_v1,
        _check_fingerprint_pool_coverage_v1,
    ):
        rejection = check(fields)
        if rejection is not None:
            return rejection
    sums = _bounded_leg_amount_sums_v1(fields.legs)
    if sums is None:
        return _binding_reject_v1(RouteBindingRejectCodeV1.AMOUNT_SUM_INVALID, ("route_legs",))
    rejection = _check_kind_totals_v1(kind, fields, sums[0], sums[1])
    if rejection is not None:
        return rejection
    return _construct_exact_binding_v1(kind, fields, sums[0], sums[1])


def derive_exact_route_binding_v1(intent: OwnedIntentV1) -> RouteBindingResultV1:
    """Derive one exact route binding from an admitted route intent.

    Cross-field checks run in the frozen order and the first failure wins:
    kind, distinct endpoints, leg coverage, leg endpoints, fingerprint pool
    coverage, bounded amount sums, then the kind-specific signed totals.
    """

    if type(intent) is not OwnedIntentV1:
        raise TypeError("route binding derivation requires an exact OwnedIntentV1")
    try:
        kind = _route_kind_of_v1(intent)
        if kind is None:
            return _binding_reject_v1(RouteBindingRejectCodeV1.KIND_MISMATCH, ())
        fields = _read_route_fields_v1(intent, kind)
        if _is_binding_reject_v1(fields):
            return fields
        return _derive_cross_field_binding_v1(kind, fields)
    except (AttributeError, TypeError, ValueError):
        return _binding_reject_v1(RouteBindingRejectCodeV1.STRUCTURAL_INVALID, ())


def _revalidated_leg_is_exact_v1(leg: RouteLegBindingV1, binding: RouteBindingV1) -> bool:
    return (
        _is_route_text_v1(leg.pool_id)
        and _is_route_text_v1(leg.asset_in)
        and _is_route_text_v1(leg.asset_out)
        and _is_route_amount_v1(leg.amount_in, 1)
        and _is_route_amount_v1(leg.amount_out, 1)
        and leg.asset_in == binding.asset_in
        and leg.asset_out == binding.asset_out
    )


def _is_bounded_route_total_v1(value: object) -> bool:
    return type(value) is int and 1 <= value <= _ROUTE_SUM_MAX_V1


def _revalidated_binding_is_exact_v1(binding: RouteBindingV1) -> bool:
    try:
        return _revalidated_binding_is_exact_inner_v1(binding)
    except (AttributeError, TypeError, ValueError):
        return False


def _revalidated_binding_is_exact_inner_v1(binding: RouteBindingV1) -> bool:
    if type(binding.kind) is not RouteKindV1:
        return False
    if not (_is_route_text_v1(binding.asset_in) and _is_route_text_v1(binding.asset_out)):
        return False
    if binding.asset_in == binding.asset_out:
        return False
    if not (
        _is_bounded_route_total_v1(binding.total_amount_in)
        and _is_bounded_route_total_v1(binding.total_amount_out)
    ):
        return False
    legs = binding.legs
    if type(legs) is not tuple or not 1 <= len(legs) <= ROUTE_LEGS_MAX_V1:
        return False
    if any(type(leg) is not RouteLegBindingV1 for leg in legs):
        return False
    if any(not _revalidated_leg_is_exact_v1(leg, binding) for leg in legs):
        return False
    fingerprints = binding.pool_fingerprints
    if type(fingerprints) is not OwnedMapV1:
        return False
    if (
        fingerprints.schema_revision != FCIS_STATE_SCHEMA_REVISION_V1
        or fingerprints.schema_id != ROUTE_POOL_FINGERPRINTS_SCHEMA_ID_V1
        or not _fingerprints_are_exact_v1(fingerprints)
    ):
        return False
    leg_pool_ids = tuple(sorted({leg.pool_id for leg in legs}))
    if leg_pool_ids != tuple(key for key, _value in fingerprints.entries):
        return False
    sums = _bounded_leg_amount_sums_v1(legs)
    return sums is not None and sums == (binding.total_amount_in, binding.total_amount_out)


def _binding_matches_intent_v1(intent: OwnedIntentV1, binding: RouteBindingV1) -> bool:
    if not _revalidated_binding_is_exact_v1(binding):
        return False
    try:
        derived = derive_exact_route_binding_v1(intent)
    except (AttributeError, TypeError, ValueError):
        return False
    return type(derived) is RouteBindingOkV1 and derived.binding == binding


def _require_exact_committed_pool_map_v1(pools: object) -> OwnedMapV1[str, CommittedPoolStateV1]:
    if type(pools) is not OwnedMapV1:
        raise TypeError("pools must be an exact committed pool map")
    exact_pools = cast(OwnedMapV1[str, CommittedPoolStateV1], pools)
    if (
        exact_pools.schema_revision != FCIS_STATE_SCHEMA_REVISION_V1
        or exact_pools.schema_id != POOL_MAP_SCHEMA_ID_V1
    ):
        raise TypeError("committed pool map schema metadata mismatch")
    return exact_pools


def route_binding_pins_exact_snapshot_observed_v1(
    intent: OwnedIntentV1,
    binding: RouteBindingV1,
    pools: OwnedMapV1[str, CommittedPoolStateV1],
) -> tuple[bool, tuple[str, ...]]:
    """Check one command-bound route binding against one committed snapshot.

    Exact command and binding types are required at the boundary.  The binding
    is recursively revalidated and rederived from the command before any pool
    lookup.  Observed reads therefore contain only canonical committed-state
    reads, never local scratch accesses during replay.
    """

    if type(intent) is not OwnedIntentV1:
        raise TypeError("exact route pin check requires an exact OwnedIntentV1")
    if type(binding) is not RouteBindingV1:
        raise TypeError("exact route pin check requires an exact RouteBindingV1")
    exact_pools = _require_exact_committed_pool_map_v1(pools)
    if not _binding_matches_intent_v1(intent, binding):
        return False, ()
    observed_pool_ids: list[str] = []
    for pool_id, fingerprint in binding.pool_fingerprints.entries:
        observed_pool_ids.append(pool_id)
        pool = exact_pools.get(pool_id)
        if pool is None or pool_state_fingerprint_committed_v1(pool) != fingerprint:
            return False, tuple(observed_pool_ids)
    return True, tuple(observed_pool_ids)


def route_binding_pins_exact_snapshot_v1(
    intent: OwnedIntentV1,
    binding: RouteBindingV1,
    pools: OwnedMapV1[str, CommittedPoolStateV1],
) -> bool:
    """Project the observed pin check to its boolean result."""

    result, _observed_pool_ids = route_binding_pins_exact_snapshot_observed_v1(
        intent, binding, pools
    )
    return result


def _preflight_exact_pools_v1(
    binding: RouteBindingV1,
    pools: OwnedMapV1[str, CommittedPoolStateV1],
) -> tuple[RouteReplayRejectV1 | None, tuple[str, ...], dict[str, CommittedPoolStateV1]]:
    observed_pool_ids: list[str] = []
    pool_values: dict[str, CommittedPoolStateV1] = {}
    for pool_id, fingerprint in binding.pool_fingerprints.entries:
        observed_pool_ids.append(pool_id)
        pool = pools.get(pool_id)
        if pool is None:
            return (
                _replay_reject_v1(RouteReplayRejectCodeV1.POOL_NOT_FOUND),
                tuple(observed_pool_ids),
                pool_values,
            )
        if type(pool) is not CommittedPoolStateV1:
            raise TypeError("exact route replay requires committed pool values")
        if pool.status.member_ordinal != POOL_STATUS_ACTIVE_MEMBER_ORDINAL_V1:
            return (
                _replay_reject_v1(RouteReplayRejectCodeV1.POOL_NOT_ACTIVE),
                tuple(observed_pool_ids),
                pool_values,
            )
        if pool_state_fingerprint_committed_v1(pool) != fingerprint:
            return (
                _replay_reject_v1(RouteReplayRejectCodeV1.POOL_STATE_DRIFT),
                tuple(observed_pool_ids),
                pool_values,
            )
        pool_values[pool_id] = pool
    return None, tuple(observed_pool_ids), pool_values


def _apply_exact_leg_v1(
    kind: RouteKindV1,
    pool: CommittedPoolStateV1,
    leg: RouteLegBindingV1,
    reserves: tuple[int, int],
) -> RouteReplayLegV1 | RouteReplayRejectCodeV1:
    reserve0, reserve1 = reserves
    if leg.asset_in == pool.asset0 and leg.asset_out == pool.asset1:
        reserve_in, reserve_out, dir_is_0_to_1 = reserve0, reserve1, True
    elif leg.asset_in == pool.asset1 and leg.asset_out == pool.asset0:
        reserve_in, reserve_out, dir_is_0_to_1 = reserve1, reserve0, False
    else:
        return RouteReplayRejectCodeV1.INVALID_PARAMS
    try:
        if kind is RouteKindV1.EXACT_IN:
            quoted, (new_in, new_out) = swap_exact_in_for_committed_pool_v1(
                pool,
                reserve_in=reserve_in,
                reserve_out=reserve_out,
                amount_in=leg.amount_in,
            )
            expected_quote = leg.amount_out
        else:
            quoted, (new_in, new_out) = swap_exact_out_for_committed_pool_v1(
                pool,
                reserve_in=reserve_in,
                reserve_out=reserve_out,
                amount_out=leg.amount_out,
            )
            expected_quote = leg.amount_in
    except (ArithmeticError, TypeError, ValueError):
        return RouteReplayRejectCodeV1.LEG_QUOTE_MISMATCH
    if quoted != expected_quote:
        return RouteReplayRejectCodeV1.LEG_QUOTE_MISMATCH
    new_reserve0, new_reserve1 = (new_in, new_out) if dir_is_0_to_1 else (new_out, new_in)
    return RouteReplayLegV1(
        leg.pool_id,
        leg.asset_in,
        leg.asset_out,
        leg.amount_in,
        leg.amount_out,
        compute_fee_total(leg.amount_in, pool.fee_bps),
        new_reserve0,
        new_reserve1,
        _ROUTE_BINDING_CONSTRUCTION_TOKEN_V1,
    )


def _replay_ok_v1(replays: tuple[RouteReplayLegV1, ...]) -> RouteReplayOkV1:
    return RouteReplayOkV1(
        replays,
        sum(leg.amount_in for leg in replays),
        sum(leg.amount_out for leg in replays),
        sum(leg.fee_paid for leg in replays),
        _ROUTE_BINDING_CONSTRUCTION_TOKEN_V1,
    )


def replay_exact_route_observed_v1(
    intent: OwnedIntentV1,
    binding: RouteBindingV1,
    pools: OwnedMapV1[str, CommittedPoolStateV1],
) -> tuple[RouteReplayResultV1, tuple[str, ...]]:
    """Replay one command-bound route binding against committed pools.

    The frozen order is: exact boundary types, recursive binding validation and
    command rederivation, canonical fingerprint preflight, then legs in their
    original semantic sequence with per-pool reserves threaded through private
    scratch state.  The observed tuple records committed preflight reads only;
    local scratch lookups are not additional state reads.
    """

    if type(intent) is not OwnedIntentV1:
        raise TypeError("exact route replay requires an exact OwnedIntentV1")
    if type(binding) is not RouteBindingV1:
        raise TypeError("exact route replay requires an exact RouteBindingV1")
    exact_pools = _require_exact_committed_pool_map_v1(pools)
    if not _binding_matches_intent_v1(intent, binding):
        return _replay_reject_v1(RouteReplayRejectCodeV1.BINDING_INVALID), ()
    preflight, preflight_reads, pool_values = _preflight_exact_pools_v1(binding, exact_pools)
    if preflight is not None:
        return preflight, preflight_reads
    scratch = {pool_id: (pool.reserve0, pool.reserve1) for pool_id, pool in pool_values.items()}
    replays: list[RouteReplayLegV1] = []
    for leg in binding.legs:
        pool = pool_values.get(leg.pool_id)
        reserves = scratch.get(leg.pool_id)
        if pool is None or reserves is None:
            return _replay_reject_v1(RouteReplayRejectCodeV1.POOL_NOT_FOUND), preflight_reads
        applied = _apply_exact_leg_v1(binding.kind, pool, leg, reserves)
        if _is_replay_reject_code_v1(applied):
            return _replay_reject_v1(applied), preflight_reads
        replays.append(applied)
        scratch[leg.pool_id] = (applied.new_reserve0, applied.new_reserve1)
    return _replay_ok_v1(tuple(replays)), preflight_reads


def replay_exact_route_v1(
    intent: OwnedIntentV1,
    binding: RouteBindingV1,
    pools: OwnedMapV1[str, CommittedPoolStateV1],
) -> RouteReplayResultV1:
    """Project the observed exact replay to its result."""

    result, _observed_pool_ids = replay_exact_route_observed_v1(intent, binding, pools)
    return result


__all__ = (
    "derive_exact_route_binding_v1",
    "replay_exact_route_observed_v1",
    "replay_exact_route_v1",
    "route_binding_pins_exact_snapshot_observed_v1",
    "route_binding_pins_exact_snapshot_v1",
)
