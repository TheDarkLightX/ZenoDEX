"""Closure-clean exact settlement index for the unmounted FCIS P4B4 path.

The public strong-settlement boundary owns recursive admission.  This module is
the admitted private sink for the next phase: it proves intent/fill coverage,
the protocol settlement order, and optional reciprocal CoW structure without
retaining mutable lookup tables.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from typing import TypeAlias, cast, final

from ..state.intent_snapshots import (
    OwnedIntentV1,
    owned_intent_field_v1,
    owned_intent_kind_text_v1,
)
from ..state.intents import IntentKind
from ..state.owned_collections import OwnedEnumV1
from .settlement_schema import fill_action_text_v1
from .settlement_snapshots import (
    OwnedFillV1,
    OwnedSettlementV1,
)


@final
class _IndexConstructionAuthorityV1:
    __slots__ = ()


_INDEX_CONSTRUCTION_AUTHORITY_V1 = _IndexConstructionAuthorityV1()


@final
@dataclass(frozen=True, slots=True)
class ExactSettlementIndexEntryV1:
    """One admitted command, declared action, and optional detailed fill."""

    intent_id: str
    intent: OwnedIntentV1
    action: OwnedEnumV1
    fill: OwnedFillV1 | None
    _construction_authority: InitVar[_IndexConstructionAuthorityV1]

    def __post_init__(
        self,
        _construction_authority: _IndexConstructionAuthorityV1,
    ) -> None:
        if _construction_authority is not _INDEX_CONSTRUCTION_AUTHORITY_V1:
            raise TypeError("settlement index entry requires controlled derivation")
        _validate_entry_graph_v1(self)


@final
@dataclass(frozen=True, slots=True)
class ExactCowPairV1:
    """One canonical reciprocal CoW pair, ordered by intent identifier."""

    lower_intent_id: str
    upper_intent_id: str
    _construction_authority: InitVar[_IndexConstructionAuthorityV1]

    def __post_init__(
        self,
        _construction_authority: _IndexConstructionAuthorityV1,
    ) -> None:
        if _construction_authority is not _INDEX_CONSTRUCTION_AUTHORITY_V1:
            raise TypeError("settlement CoW pair requires controlled derivation")
        if (
            type(self.lower_intent_id) is not str
            or type(self.upper_intent_id) is not str
            or not self.lower_intent_id
            or self.lower_intent_id >= self.upper_intent_id
        ):
            raise ValueError("settlement CoW pair must use canonical distinct intent IDs")


@final
@dataclass(frozen=True, slots=True)
class ExactSettlementIndexV1:
    """Immutable index derived from one admitted command/settlement lineage."""

    input_intents: tuple[OwnedIntentV1, ...]
    settlement: OwnedSettlementV1
    entries: tuple[ExactSettlementIndexEntryV1, ...]
    cow_pairs: tuple[ExactCowPairV1, ...]
    allow_cow_netting: bool
    _construction_authority: InitVar[_IndexConstructionAuthorityV1]

    def __post_init__(
        self,
        _construction_authority: _IndexConstructionAuthorityV1,
    ) -> None:
        if _construction_authority is not _INDEX_CONSTRUCTION_AUTHORITY_V1:
            raise TypeError("settlement index requires controlled derivation")
        _validate_index_shape_v1(self)


@final
@dataclass(frozen=True, slots=True)
class ExactSettlementIndexRejectV1:
    """Stable index rejection with no replay or successor authority."""

    reason: str
    _construction_authority: InitVar[_IndexConstructionAuthorityV1]

    def __post_init__(
        self,
        _construction_authority: _IndexConstructionAuthorityV1,
    ) -> None:
        if _construction_authority is not _INDEX_CONSTRUCTION_AUTHORITY_V1:
            raise TypeError("settlement index rejection requires controlled derivation")
        if type(self.reason) is not str or not self.reason:
            raise TypeError("settlement index rejection requires an exact reason")


ExactSettlementIndexResultV1: TypeAlias = ExactSettlementIndexV1 | ExactSettlementIndexRejectV1


@final
@dataclass(frozen=True, slots=True)
class _CowEntryV1:
    intent_id: str
    pool_id: str
    asset_in: str
    asset_out: str
    amount_in_filled: int
    amount_out_filled: int


def _reject_v1(reason: str) -> ExactSettlementIndexRejectV1:
    return ExactSettlementIndexRejectV1(
        reason,
        _INDEX_CONSTRUCTION_AUTHORITY_V1,
    )


def _render_string_list_v1(values: tuple[str, ...]) -> str:
    return "[" + ", ".join(repr(value) for value in values) + "]"


def _validate_entry_graph_v1(entry: ExactSettlementIndexEntryV1) -> None:
    if type(entry.intent_id) is not str or not entry.intent_id:
        raise TypeError("settlement index intent ID must be an exact nonempty string")
    if type(entry.intent) is not OwnedIntentV1 or entry.intent.intent_id != entry.intent_id:
        raise TypeError("settlement index intent lineage mismatch")
    action_text = fill_action_text_v1(entry.action)
    if action_text == "FILL":
        fill = entry.fill
        if type(fill) is not OwnedFillV1:
            raise TypeError("filled settlement index entry requires one exact fill")
        exact_fill = cast(OwnedFillV1, fill)
        if (
            exact_fill.intent_id != entry.intent_id
            or fill_action_text_v1(exact_fill.action) != action_text
        ):
            raise TypeError("settlement index fill lineage mismatch")
        return
    if action_text != "REJECT" or entry.fill is not None:
        raise TypeError("rejected settlement index entry cannot retain a detailed fill")


def _validate_index_shape_v1(index: ExactSettlementIndexV1) -> None:
    if type(index.input_intents) is not tuple or any(
        type(intent) is not OwnedIntentV1 for intent in index.input_intents
    ):
        raise TypeError("settlement index input intents must be an exact tuple")
    if type(index.settlement) is not OwnedSettlementV1:
        raise TypeError("settlement index settlement must be exact")
    if type(index.entries) is not tuple or any(
        type(entry) is not ExactSettlementIndexEntryV1 for entry in index.entries
    ):
        raise TypeError("settlement index entries must be exact")
    if type(index.cow_pairs) is not tuple or any(
        type(pair) is not ExactCowPairV1 for pair in index.cow_pairs
    ):
        raise TypeError("settlement index CoW pairs must be exact")
    if type(index.allow_cow_netting) is not bool:
        raise TypeError("settlement index CoW policy must be an exact Boolean")
    for entry in index.entries:
        _validate_entry_graph_v1(entry)
    input_ids = tuple(intent.intent_id for intent in index.input_intents)
    entry_ids = tuple(entry.intent_id for entry in index.entries)
    if _has_duplicate_ids_v1(input_ids) or sorted(input_ids) != sorted(entry_ids):
        raise ValueError("settlement index intent coverage drift")
    expected_fill_ids = tuple(
        entry.intent_id for entry in index.entries if fill_action_text_v1(entry.action) == "FILL"
    )
    if tuple(fill.intent_id for fill in index.settlement.fills) != expected_fill_ids:
        raise ValueError("settlement index fill order drift")
    pair_keys = tuple((pair.lower_intent_id, pair.upper_intent_id) for pair in index.cow_pairs)
    if pair_keys != tuple(sorted(pair_keys)) or _has_duplicate_pairs_v1(pair_keys):
        raise ValueError("settlement index CoW pair order drift")


def _has_duplicate_ids_v1(values: tuple[str, ...]) -> bool:
    return any(
        values[left] == values[right]
        for left in range(len(values))
        for right in range(left + 1, len(values))
    )


def _has_duplicate_pairs_v1(values: tuple[tuple[str, str], ...]) -> bool:
    return any(
        values[left] == values[right]
        for left in range(len(values))
        for right in range(left + 1, len(values))
    )


def _intent_lookup_v1(
    intents: tuple[OwnedIntentV1, ...],
) -> dict[str, OwnedIntentV1] | ExactSettlementIndexRejectV1:
    intent_lookup = {intent.intent_id: intent for intent in intents}
    if len(intent_lookup) != len(intents):
        return _reject_v1("duplicate intent_id in input intents")
    return intent_lookup


def _included_lookup_v1(
    settlement: OwnedSettlementV1,
    intent_lookup: dict[str, OwnedIntentV1],
) -> dict[str, OwnedEnumV1] | ExactSettlementIndexRejectV1:
    included_lookup = {intent_id: action for intent_id, action in settlement.included_intents}
    missing = tuple(
        sorted(intent_id for intent_id in intent_lookup if intent_id not in included_lookup)
    )
    extra = tuple(
        sorted(intent_id for intent_id in included_lookup if intent_id not in intent_lookup)
    )
    if missing or extra:
        return _reject_v1(
            "settlement included_intents mismatch: "
            f"missing={_render_string_list_v1(missing)} "
            f"extra={_render_string_list_v1(extra)}"
        )
    if len(included_lookup) != len(settlement.included_intents):
        return _reject_v1("settlement included_intents contains duplicate intent_id entries")
    return included_lookup


def _fill_lookup_v1(
    settlement: OwnedSettlementV1,
    intent_lookup: dict[str, OwnedIntentV1],
) -> dict[str, OwnedFillV1] | ExactSettlementIndexRejectV1:
    fill_lookup = {fill.intent_id: fill for fill in settlement.fills}
    if len(fill_lookup) != len(settlement.fills):
        return _reject_v1("settlement fills contains duplicate intent_id entries")
    extra = tuple(sorted(intent_id for intent_id in fill_lookup if intent_id not in intent_lookup))
    if extra:
        return _reject_v1(
            "settlement fills contains intent_ids not in input intents: "
            f"{_render_string_list_v1(extra)}"
        )
    return fill_lookup


def _build_entries_v1(
    settlement: OwnedSettlementV1,
    intent_lookup: dict[str, OwnedIntentV1],
    fill_lookup: dict[str, OwnedFillV1],
) -> tuple[ExactSettlementIndexEntryV1, ...] | ExactSettlementIndexRejectV1:
    entries: list[ExactSettlementIndexEntryV1] = []
    for intent_id, action in settlement.included_intents:
        fill = fill_lookup.get(intent_id)
        action_text = fill_action_text_v1(action)
        if fill is None and action_text == "FILL":
            return _reject_v1(f"missing Fill for filled intent_id: {intent_id}")
        if fill is not None and fill_action_text_v1(fill.action) != action_text:
            return _reject_v1(
                "Fill.action mismatch for intent_id="
                f"{intent_id}: {fill_action_text_v1(fill.action)} != {action_text}"
            )
        if fill is not None and action_text == "REJECT":
            return _reject_v1(f"unexpected Fill for rejected intent_id: {intent_id}")
        entries.append(
            ExactSettlementIndexEntryV1(
                intent_id,
                intent_lookup[intent_id],
                action,
                fill,
                _INDEX_CONSTRUCTION_AUTHORITY_V1,
            )
        )
    expected_fill_ids = tuple(
        entry.intent_id for entry in entries if fill_action_text_v1(entry.action) == "FILL"
    )
    if tuple(fill.intent_id for fill in settlement.fills) != expected_fill_ids:
        return _reject_v1("settlement fills must follow included FILL order")
    return tuple(entries)


def _entry_for_id_v1(
    entries: tuple[ExactSettlementIndexEntryV1, ...],
    intent_id: str,
) -> ExactSettlementIndexEntryV1:
    for entry in entries:
        if entry.intent_id == intent_id:
            return entry
    raise RuntimeError("settlement index coverage invariant failed")


def _cow_entry_v1(
    entry: ExactSettlementIndexEntryV1,
) -> _CowEntryV1 | ExactSettlementIndexRejectV1:
    intent = entry.intent
    intent_id = entry.intent_id
    fill = entry.fill
    if type(fill) is not OwnedFillV1:
        return _reject_v1(f"COW_NETTED requires filled action: intent_id={intent_id}")
    exact_fill = cast(OwnedFillV1, fill)
    if fill_action_text_v1(exact_fill.action) != "FILL":
        return _reject_v1(f"COW_NETTED requires filled action: intent_id={intent_id}")
    if owned_intent_kind_text_v1(intent) != IntentKind.SWAP_EXACT_IN.value:
        return _reject_v1(f"COW_NETTED only supported for SWAP_EXACT_IN: intent_id={intent_id}")
    pool_id = owned_intent_field_v1(intent, "pool_id")
    if type(pool_id) is not str or not pool_id:
        return _reject_v1(f"missing pool_id for intent_id={intent_id}")
    asset_in = owned_intent_field_v1(intent, "asset_in")
    asset_out = owned_intent_field_v1(intent, "asset_out")
    if type(asset_in) is not str or type(asset_out) is not str:
        return _reject_v1(f"invalid asset_in/out for intent_id={intent_id}")
    amount_in = owned_intent_field_v1(intent, "amount_in")
    minimum_out = owned_intent_field_v1(intent, "min_amount_out")
    if type(amount_in) is not int or amount_in <= 0:
        return _reject_v1(f"invalid amount_in for intent_id={intent_id}")
    if type(minimum_out) is not int or minimum_out < 0:
        return _reject_v1(f"invalid min_amount_out for intent_id={intent_id}")
    if exact_fill.fee_paid is not None and exact_fill.fee_paid != 0:
        return _reject_v1(f"COW_NETTED fee_paid must be 0: intent_id={intent_id}")
    if type(exact_fill.amount_in_filled) is not int or exact_fill.amount_in_filled != amount_in:
        return _reject_v1(f"COW_NETTED amount_in_filled mismatch: intent_id={intent_id}")
    if type(exact_fill.amount_out_filled) is not int:
        return _reject_v1(f"COW_NETTED amount_out_filled invalid: intent_id={intent_id}")
    if exact_fill.amount_out_filled < minimum_out:
        return _reject_v1(f"COW_NETTED slippage: intent_id={intent_id}")
    return _CowEntryV1(
        intent_id,
        pool_id,
        asset_in,
        asset_out,
        exact_fill.amount_in_filled,
        exact_fill.amount_out_filled,
    )


def _is_reciprocal_v1(left: _CowEntryV1, right: _CowEntryV1) -> bool:
    return (
        left.intent_id != right.intent_id
        and left.pool_id == right.pool_id
        and left.asset_in == right.asset_out
        and left.asset_out == right.asset_in
        and left.amount_in_filled == right.amount_out_filled
        and left.amount_out_filled == right.amount_in_filled
    )


def _derive_cow_pairs_v1(
    entries: tuple[ExactSettlementIndexEntryV1, ...],
    allow_cow_netting: bool,
) -> tuple[ExactCowPairV1, ...] | ExactSettlementIndexRejectV1:
    cow_ids = tuple(
        entry.intent_id
        for entry in entries
        if entry.fill is not None and entry.fill.reason == "COW_NETTED"
    )
    if not cow_ids:
        return ()
    if not allow_cow_netting:
        return _reject_v1(f"COW_NETTED not allowed for intent_id={cow_ids[0]}")
    cow_entries: list[_CowEntryV1] = []
    for intent_id in cow_ids:
        candidate = _cow_entry_v1(_entry_for_id_v1(entries, intent_id))
        if type(candidate) is ExactSettlementIndexRejectV1:
            return candidate
        cow_entries.append(candidate)
    pair_for: dict[str, str] = {}
    for entry in cow_entries:
        matches = tuple(
            candidate.intent_id for candidate in cow_entries if _is_reciprocal_v1(entry, candidate)
        )
        if len(matches) != 1:
            return _reject_v1(
                "COW_NETTED fill requires exactly one reciprocal counterparty: "
                f"intent_id={entry.intent_id} matches={_render_string_list_v1(matches)}"
            )
        pair_for[entry.intent_id] = matches[0]
    for intent_id, counterparty_id in pair_for.items():
        if pair_for.get(counterparty_id) != intent_id:
            return _reject_v1(f"COW_NETTED reciprocal pair is not symmetric: intent_id={intent_id}")
    pair_keys = tuple(
        sorted(
            (intent_id, counterparty_id)
            for intent_id, counterparty_id in pair_for.items()
            if intent_id < counterparty_id
        )
    )
    return tuple(
        ExactCowPairV1(left, right, _INDEX_CONSTRUCTION_AUTHORITY_V1) for left, right in pair_keys
    )


def _validate_route_order_v1(
    entries: tuple[ExactSettlementIndexEntryV1, ...],
) -> ExactSettlementIndexRejectV1 | None:
    route_kinds = (IntentKind.ROUTE_EXACT_IN.value, IntentKind.ROUTE_EXACT_OUT.value)
    route_ids = tuple(
        entry.intent_id
        for entry in entries
        if owned_intent_kind_text_v1(entry.intent) in route_kinds
    )
    if not route_ids:
        return None
    if route_ids != tuple(sorted(route_ids)):
        return _reject_v1("route intents must be settled in ascending intent_id order")
    previous_phase = 0
    for entry in entries:
        kind = owned_intent_kind_text_v1(entry.intent)
        phase = 0 if kind == IntentKind.CREATE_POOL.value else 1 if kind in route_kinds else 2
        if phase < previous_phase:
            return _reject_v1(
                "non-canonical settlement phase order at intent_id="
                f"{entry.intent_id}: routes require CREATE_POOL before route "
                "before other pool intents"
            )
        previous_phase = phase
    return None


def derive_exact_settlement_index_admitted_v1(
    settlement: OwnedSettlementV1,
    intents: tuple[OwnedIntentV1, ...],
    *,
    allow_cow_netting: bool,
) -> ExactSettlementIndexResultV1:
    """Derive one index from recursively admitted exact inputs.

    Rejection precedence matches the mixed validator through action matching,
    then applies the frozen P4B4 no-REJECT-detail and ordering laws before CoW
    and route replay.  Local dictionaries are bounded scratch and never escape.
    """

    if type(settlement) is not OwnedSettlementV1:
        raise TypeError("settlement index requires exact OwnedSettlementV1")
    if type(intents) is not tuple or any(type(intent) is not OwnedIntentV1 for intent in intents):
        raise TypeError("settlement index requires an exact OwnedIntentV1 tuple")
    if type(allow_cow_netting) is not bool:
        raise TypeError("allow_cow_netting must be an exact Boolean")
    intent_lookup = _intent_lookup_v1(intents)
    if type(intent_lookup) is ExactSettlementIndexRejectV1:
        return intent_lookup
    included_lookup = _included_lookup_v1(settlement, intent_lookup)
    if type(included_lookup) is ExactSettlementIndexRejectV1:
        return included_lookup
    fill_lookup = _fill_lookup_v1(settlement, intent_lookup)
    if type(fill_lookup) is ExactSettlementIndexRejectV1:
        return fill_lookup
    entries = _build_entries_v1(settlement, intent_lookup, fill_lookup)
    if type(entries) is ExactSettlementIndexRejectV1:
        return entries
    cow_pairs = _derive_cow_pairs_v1(entries, allow_cow_netting)
    if type(cow_pairs) is ExactSettlementIndexRejectV1:
        return cow_pairs
    route_reject = _validate_route_order_v1(entries)
    if route_reject is not None:
        return route_reject
    return ExactSettlementIndexV1(
        intents,
        settlement,
        entries,
        cow_pairs,
        allow_cow_netting,
        _INDEX_CONSTRUCTION_AUTHORITY_V1,
    )


__all__ = (
    "ExactCowPairV1",
    "ExactSettlementIndexEntryV1",
    "ExactSettlementIndexRejectV1",
    "ExactSettlementIndexResultV1",
    "ExactSettlementIndexV1",
    "derive_exact_settlement_index_admitted_v1",
)
