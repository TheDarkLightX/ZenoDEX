#!/usr/bin/env python3
"""Validate the research-only Global Economic Delta Algebra V2.

The checker closes the eight event-level delta shapes declared by the G1
semantic inventory.  It validates owned JSON values and emits deterministic
canonical bytes and a domain-separated root.  It grants no settlement,
publication, proof, release, profile-selection, or production authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from types import MappingProxyType
from typing import Final, Mapping, Sequence

if __package__:
    from tools import global_economic_delta_v2_references as _references
    from tools import global_economic_delta_v2_types as _types
else:
    import global_economic_delta_v2_references as _references
    import global_economic_delta_v2_types as _types

I128_MAX = _types.I128_MAX
MAX_EVENTS_V2 = _types.MAX_EVENTS_V2
MAX_INPUT_BYTES_V2 = _types.MAX_INPUT_BYTES_V2
MAX_SOURCE_BINDINGS_V2 = _types.MAX_SOURCE_BINDINGS_V2
ROOT_DOMAIN_V2 = _types.ROOT_DOMAIN_V2
SCHEMA_V2 = _types.SCHEMA_V2
DeltaRejectCodeV2 = _types.DeltaRejectCodeV2
DeltaValidationErrorV2 = _types.DeltaValidationErrorV2
ScalarV2 = _types.ScalarV2
_StructuralDeltaPlanDataV2 = _types._StructuralDeltaPlanDataV2
ZeroPolicyV2 = _types.ZeroPolicyV2
_AMOUNT_FIELD_ORDER = _types._AMOUNT_FIELD_ORDER
_AMOUNT_FIELDS = _types._AMOUNT_FIELDS
_ID_RE = _types._ID_RE
_ROOT_FIELD_ORDER = _types._ROOT_FIELD_ORDER
_ROOT_FIELDS = _types._ROOT_FIELDS
_ROOT_RE = _types._ROOT_RE
_SOURCE_BINDING_FIELDS = _types._SOURCE_BINDING_FIELDS
_SOURCE_KINDS = _types._SOURCE_KINDS
_VARIANT_FIELDS = _types._VARIANT_FIELDS
validate_source_references_v2 = _references.validate_source_references_v2


def _reject(code: DeltaRejectCodeV2, detail: str) -> None:
    raise DeltaValidationErrorV2(code, detail)


def _owned_exact_mapping(
    value: object,
    *,
    expected: frozenset[str],
    label: str = "event",
) -> dict[str, object]:
    if type(value) is not dict:
        _reject(DeltaRejectCodeV2.EVENT_TYPE_INVALID, f"{label} must be an exact object")
    owned = dict(value)
    if not all(type(key) is str for key in owned):
        _reject(DeltaRejectCodeV2.EVENT_FIELDS_INVALID, f"{label} keys must be strings")
    if frozenset(owned) != expected:
        _reject(DeltaRejectCodeV2.EVENT_FIELDS_INVALID, f"{label} field set is not closed")
    return owned


def _require_id(value: object, *, field: str) -> str:
    if type(value) is not str or _ID_RE.fullmatch(value) is None:
        _reject(DeltaRejectCodeV2.IDENTIFIER_INVALID, f"{field} is not canonical")
    return value


def _require_root(value: object, *, field: str) -> str:
    if (
        type(value) is not str
        or _ROOT_RE.fullmatch(value) is None
        or value == "sha256:" + "0" * 64
    ):
        _reject(DeltaRejectCodeV2.ROOT_INVALID, f"{field} is not a canonical root")
    return value


def _require_atoms(
    value: object,
    *,
    field: str,
    zero_policy: ZeroPolicyV2 = ZeroPolicyV2.FORBID,
) -> int:
    if type(value) is not int:
        _reject(DeltaRejectCodeV2.AMOUNT_TYPE_INVALID, f"{field} must be an exact integer")
    minimum = 0 if zero_policy is ZeroPolicyV2.ALLOW else 1
    if value < minimum or value > I128_MAX:
        _reject(DeltaRejectCodeV2.AMOUNT_OUT_OF_RANGE, f"{field} is outside its range")
    return value


def _validate_identifiers(event: Mapping[str, object]) -> None:
    for field in _ROOT_FIELD_ORDER:
        if field in event:
            _require_root(event[field], field=field)
    for field in sorted(event):
        if field not in _ROOT_FIELDS | _AMOUNT_FIELDS | {"delta_class", "direction"}:
            _require_id(event[field], field=field)


def _validate_internal_transfer(event: Mapping[str, object]) -> None:
    source = (event["source_owner"], event["source_ledger_allocation"])
    destination = (event["destination_owner"], event["destination_ledger_allocation"])
    if source == destination:
        _reject(
            DeltaRejectCodeV2.SOURCE_EQUALS_DESTINATION,
            "internal transfer source and destination must differ",
        )


def _validate_liability(event: Mapping[str, object]) -> None:
    pre_atoms = _require_atoms(
        event["pre_atoms"], field="pre_atoms", zero_policy=ZeroPolicyV2.ALLOW
    )
    post_atoms = _require_atoms(
        event["post_atoms"], field="post_atoms", zero_policy=ZeroPolicyV2.ALLOW
    )
    amount_atoms = _require_atoms(event["amount_atoms"], field="amount_atoms")
    direction = event["direction"]
    increase = direction == "increase" and post_atoms > pre_atoms
    decrease = direction == "decrease" and pre_atoms > post_atoms
    if not (increase or decrease) or abs(post_atoms - pre_atoms) != amount_atoms:
        _reject(
            DeltaRejectCodeV2.LIABILITY_RELATION_INVALID,
            "liability direction and before/after values do not derive the amount",
        )


def _validate_slash(event: Mapping[str, object]) -> None:
    amount_atoms = _require_atoms(event["amount_atoms"], field="amount_atoms")
    beneficiary_atoms = _require_atoms(
        event["beneficiary_atoms"],
        field="beneficiary_atoms",
        zero_policy=ZeroPolicyV2.ALLOW,
    )
    residue_atoms = _require_atoms(
        event["residue_atoms"],
        field="residue_atoms",
        zero_policy=ZeroPolicyV2.ALLOW,
    )
    if beneficiary_atoms + residue_atoms != amount_atoms:
        _reject(
            DeltaRejectCodeV2.SLASH_PARTITION_MISMATCH,
            "slash beneficiary and residue must partition the exact amount",
        )


def _validate_refund(event: Mapping[str, object]) -> None:
    source = (event["source_owner"], event["source_ledger_allocation"])
    destination = (event["refund_owner"], event["refund_ledger_allocation"])
    if source == destination:
        _reject(
            DeltaRejectCodeV2.SOURCE_EQUALS_DESTINATION,
            "refund source and destination must differ",
        )
    if event["economic_event"] == event["source_event"]:
        _reject(
            DeltaRejectCodeV2.SELF_REFERENTIAL_EVENT,
            "refund cannot cite itself as its source event",
        )


def _validate_external_in(event: Mapping[str, object]) -> None:
    if event["economic_event"] == event["source_effect"]:
        _reject(
            DeltaRejectCodeV2.SELF_REFERENTIAL_EVENT,
            "external ingress cannot cite itself as its source effect",
        )


def _validate_external_out(event: Mapping[str, object]) -> None:
    related = {event["ancestor_claim_event"], event["destination_effect"]}
    if event["economic_event"] in related or len(related) != 2:
        _reject(
            DeltaRejectCodeV2.SELF_REFERENTIAL_EVENT,
            "external egress event, ancestor claim, and destination effect must differ",
        )


_RELATION_VALIDATORS: Final = {
    "external_in": _validate_external_in,
    "external_out": _validate_external_out,
    "internal_transfer": _validate_internal_transfer,
    "liability": _validate_liability,
    "refund": _validate_refund,
    "slash": _validate_slash,
}


def _validate_variant_relations(event: Mapping[str, object]) -> None:
    validator = _RELATION_VALIDATORS.get(event["delta_class"])
    if validator is not None:
        validator(event)


def _validate_event(value: object) -> dict[str, ScalarV2]:
    if type(value) is not dict:
        _reject(DeltaRejectCodeV2.EVENT_TYPE_INVALID, "event must be an exact object")
    raw_class = value.get("delta_class")
    if type(raw_class) is not str or raw_class not in _VARIANT_FIELDS:
        _reject(DeltaRejectCodeV2.DELTA_CLASS_INVALID, "delta class is not closed")
    event = _owned_exact_mapping(value, expected=_VARIANT_FIELDS[raw_class])
    if raw_class == "liability" and event["direction"] not in {"increase", "decrease"}:
        _reject(DeltaRejectCodeV2.DIRECTION_INVALID, "liability direction is not closed")
    _validate_identifiers(event)
    for field in _AMOUNT_FIELD_ORDER:
        if field in event:
            zero_policy = (
                ZeroPolicyV2.FORBID
                if field == "amount_atoms"
                else ZeroPolicyV2.ALLOW
            )
            _require_atoms(event[field], field=field, zero_policy=zero_policy)
    _validate_variant_relations(event)
    return {key: event[key] for key in sorted(event)}  # type: ignore[return-value]


def _validate_source_binding(value: object) -> dict[str, ScalarV2]:
    binding = _owned_exact_mapping(
        value,
        expected=_SOURCE_BINDING_FIELDS,
        label="source binding",
    )
    _require_root(binding["source_root"], field="source_root")
    source_kind = binding["source_kind"]
    if type(source_kind) is not str or source_kind not in _SOURCE_KINDS:
        _reject(DeltaRejectCodeV2.SOURCE_KIND_INVALID, "source kind is not closed")
    _require_id(binding["asset"], field="asset")
    _require_atoms(binding["amount_atoms"], field="amount_atoms")
    return {key: binding[key] for key in sorted(binding)}  # type: ignore[return-value]


def _canonical_bytes(
    events: Sequence[Mapping[str, ScalarV2]],
    source_bindings: Sequence[Mapping[str, ScalarV2]],
) -> bytes:
    document = {
        "events": [dict(event) for event in events],
        "schema": SCHEMA_V2,
        "source_bindings": [dict(binding) for binding in source_bindings],
    }
    return (
        json.dumps(document, ensure_ascii=True, separators=(",", ":"), sort_keys=True)
        + "\n"
    ).encode("ascii")


def validate_plan_v2(value: object) -> _StructuralDeltaPlanDataV2:
    """Return one structurally valid owned plan or a typed no-candidate reject."""

    if type(value) is not dict:
        _reject(DeltaRejectCodeV2.PLAN_TYPE_INVALID, "plan must be an exact object")
    owned_plan = dict(value)
    if not all(type(key) is str for key in owned_plan):
        _reject(DeltaRejectCodeV2.PLAN_FIELDS_INVALID, "plan keys must be strings")
    if frozenset(owned_plan) != {"schema", "events", "source_bindings"}:
        _reject(DeltaRejectCodeV2.PLAN_FIELDS_INVALID, "plan field set is not closed")
    if type(owned_plan["schema"]) is not str:
        _reject(DeltaRejectCodeV2.SCHEMA_TYPE_INVALID, "plan schema must be a string")
    if owned_plan["schema"] != SCHEMA_V2:
        _reject(DeltaRejectCodeV2.SCHEMA_MISMATCH, "plan schema is not V2")
    raw_bindings = owned_plan["source_bindings"]
    if type(raw_bindings) is not list:
        _reject(
            DeltaRejectCodeV2.EVENTS_TYPE_INVALID,
            "source bindings must be a JSON array",
        )
    if len(raw_bindings) > MAX_SOURCE_BINDINGS_V2:
        _reject(
            DeltaRejectCodeV2.SOURCE_BINDING_COUNT_OUT_OF_RANGE,
            "a delta plan may bind at most 64 source occurrences",
        )
    raw_events = owned_plan["events"]
    if type(raw_events) is not list:
        _reject(DeltaRejectCodeV2.EVENTS_TYPE_INVALID, "events must be a JSON array")
    if not raw_events:
        _reject(DeltaRejectCodeV2.EMPTY_PLAN, "a delta plan must contain an event")
    if len(raw_events) > MAX_EVENTS_V2:
        _reject(
            DeltaRejectCodeV2.EVENT_COUNT_OUT_OF_RANGE,
            "a delta plan may contain at most 64 events",
        )
    source_bindings = tuple(
        _validate_source_binding(binding) for binding in raw_bindings
    )
    events = tuple(_validate_event(event) for event in raw_events)
    event_ids = tuple(event["economic_event"] for event in events)
    if len(event_ids) != len(set(event_ids)):
        _reject(DeltaRejectCodeV2.DUPLICATE_EVENT, "economic event IDs must be unique")
    if event_ids != tuple(sorted(event_ids)):
        _reject(
            DeltaRejectCodeV2.NONCANONICAL_EVENT_ORDER,
            "economic events must be ordered by root",
        )
    validate_source_references_v2(source_bindings, events, frozenset(event_ids))
    canonical_bytes = _canonical_bytes(events, source_bindings)
    digest = hashlib.sha256(ROOT_DOMAIN_V2 + canonical_bytes).hexdigest()
    frozen_events = tuple(MappingProxyType(dict(event)) for event in events)
    frozen_bindings = tuple(
        MappingProxyType(dict(binding)) for binding in source_bindings
    )
    return _StructuralDeltaPlanDataV2(
        events=frozen_events,
        source_bindings=frozen_bindings,
        canonical_bytes=canonical_bytes,
        root=f"sha256:{digest}",
    )


_BYTE_DECODE_REJECTS: Final = frozenset(
    {
        DeltaRejectCodeV2.PLAN_TYPE_INVALID,
        DeltaRejectCodeV2.PLAN_FIELDS_INVALID,
        DeltaRejectCodeV2.SCHEMA_TYPE_INVALID,
        DeltaRejectCodeV2.EVENTS_TYPE_INVALID,
        DeltaRejectCodeV2.EVENT_TYPE_INVALID,
        DeltaRejectCodeV2.EVENT_FIELDS_INVALID,
        DeltaRejectCodeV2.DELTA_CLASS_INVALID,
        DeltaRejectCodeV2.IDENTIFIER_INVALID,
        DeltaRejectCodeV2.ROOT_INVALID,
        DeltaRejectCodeV2.AMOUNT_TYPE_INVALID,
        DeltaRejectCodeV2.SOURCE_KIND_INVALID,
        DeltaRejectCodeV2.DIRECTION_INVALID,
    }
)


def decode_delta_plan_bytes_v2(input_bytes: bytes) -> _StructuralDeltaPlanDataV2:
    """Decode exact bytes with the same coarse malformed-input ABI as Rust."""

    if type(input_bytes) is not bytes:
        _reject(DeltaRejectCodeV2.DECODE_INVALID, "input must be exact bytes")
    if len(input_bytes) > MAX_INPUT_BYTES_V2:
        _reject(DeltaRejectCodeV2.INPUT_TOO_LARGE, "delta plan exceeds the byte limit")
    duplicates: list[str] = []

    def hook(pairs: list[tuple[str, object]]) -> dict[str, object]:
        result: dict[str, object] = {}
        for key, value in pairs:
            if key in result:
                duplicates.append(key)
            result[key] = value
        return result

    try:
        text = input_bytes.decode("utf-8")
        value = json.loads(text, object_pairs_hook=hook)
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError) as exc:
        _reject(DeltaRejectCodeV2.DECODE_INVALID, f"input is not one JSON plan: {exc}")
    if duplicates:
        _reject(
            DeltaRejectCodeV2.DECODE_INVALID,
            f"duplicate JSON keys: {sorted(set(duplicates))}",
        )
    try:
        return validate_plan_v2(value)
    except DeltaValidationErrorV2 as exc:
        if exc.code in _BYTE_DECODE_REJECTS:
            _reject(DeltaRejectCodeV2.DECODE_INVALID, str(exc))
        raise


def _read_bounded(path: Path) -> bytes:
    with path.open("rb") as stream:
        return stream.read(MAX_INPUT_BYTES_V2 + 1)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    try:
        plan = decode_delta_plan_bytes_v2(_read_bounded(args.input))
        report = {
            "ok": True,
            "schema": SCHEMA_V2,
            "event_count": len(plan.events),
            "source_binding_count": len(plan.source_bindings),
            "root": plan.root,
            "production_ready": False,
            "production_authority": "NONE",
        }
    except (OSError, json.JSONDecodeError, DeltaValidationErrorV2) as exc:
        report = {
            "ok": False,
            "schema": SCHEMA_V2,
            "error": str(exc),
            "production_ready": False,
            "production_authority": "NONE",
        }
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print("PASS" if report["ok"] else "FAIL")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
