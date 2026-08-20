"""Exact reference-graph checks for declarative V2 source bindings."""

from __future__ import annotations

from collections.abc import Mapping, Sequence

if __package__:
    from tools import global_economic_delta_v2_types as _types
else:
    import global_economic_delta_v2_types as _types

DeltaRejectCodeV2 = _types.DeltaRejectCodeV2
DeltaValidationErrorV2 = _types.DeltaValidationErrorV2
ScalarV2 = _types.ScalarV2
_SOURCE_EXPECTATIONS = _types._SOURCE_EXPECTATIONS


def _reject(code: DeltaRejectCodeV2, detail: str) -> None:
    raise DeltaValidationErrorV2(code, detail)


def _index_sources(
    source_bindings: Sequence[Mapping[str, ScalarV2]],
) -> tuple[tuple[ScalarV2, ...], dict[ScalarV2, Mapping[str, ScalarV2]]]:
    source_roots = tuple(binding["source_root"] for binding in source_bindings)
    if len(source_roots) != len(set(source_roots)):
        _reject(
            DeltaRejectCodeV2.SOURCE_REFERENCE_REUSED,
            "source occurrence roots must be unique",
        )
    if source_roots != tuple(sorted(source_roots)):
        _reject(
            DeltaRejectCodeV2.NONCANONICAL_SOURCE_ORDER,
            "source bindings must be ordered by root",
        )
    return source_roots, {
        binding["source_root"]: binding for binding in source_bindings
    }


def _check_root_domains(
    source_roots: tuple[ScalarV2, ...],
    events: Sequence[Mapping[str, ScalarV2]],
    event_ids: frozenset[ScalarV2],
) -> None:
    output_roots = tuple(
        event["destination_effect"]
        for event in events
        if event["delta_class"] == "external_out"
    )
    if (
        len(output_roots) != len(set(output_roots))
        or event_ids.intersection(output_roots)
        or set(source_roots).intersection(output_roots)
        or event_ids.intersection(source_roots)
    ):
        _reject(
            DeltaRejectCodeV2.REFERENCE_ROOT_CONFLICT,
            "events, source occurrences, and output effects must be disjoint",
        )


def _consume_sources(
    binding_by_root: Mapping[ScalarV2, Mapping[str, ScalarV2]],
    events: Sequence[Mapping[str, ScalarV2]],
    event_ids: frozenset[ScalarV2],
) -> set[ScalarV2]:
    consumed: set[ScalarV2] = set()
    for event in events:
        expectation = _SOURCE_EXPECTATIONS.get(event["delta_class"])
        if expectation is None:
            continue
        field, source_kind = expectation
        source_root = event[field]
        if source_root in event_ids:
            _reject(
                DeltaRejectCodeV2.REFERENCE_ROOT_CONFLICT,
                "source references cannot cite events from the candidate plan",
            )
        binding = binding_by_root.get(source_root)
        if binding is None or (
            binding["source_kind"] != source_kind
            or binding["asset"] != event["asset"]
            or binding["amount_atoms"] != event["amount_atoms"]
        ):
            _reject(
                DeltaRejectCodeV2.SOURCE_REFERENCE_INVALID,
                "source kind, asset, and amount must match the consuming event",
            )
        if source_root in consumed:
            _reject(
                DeltaRejectCodeV2.SOURCE_REFERENCE_REUSED,
                "one source occurrence cannot be consumed twice in a plan",
            )
        consumed.add(source_root)
    return consumed


def validate_source_references_v2(
    source_bindings: Sequence[Mapping[str, ScalarV2]],
    events: Sequence[Mapping[str, ScalarV2]],
    event_ids: frozenset[ScalarV2],
) -> None:
    source_roots, binding_by_root = _index_sources(source_bindings)
    _check_root_domains(source_roots, events, event_ids)
    consumed = _consume_sources(binding_by_root, events, event_ids)
    if consumed != set(source_roots):
        _reject(
            DeltaRejectCodeV2.SOURCE_BINDING_UNUSED,
            "every source binding must be consumed exactly once",
        )
