"""Defensively owned snapshots for the governed economic profile graph."""

from __future__ import annotations

from dataclasses import fields, replace
from enum import Enum
from typing import Any

from .global_settlement_types_v1 import (
    EconomicProfileSnapshotV1,
    EvidenceStatusV1,
    LaneCoordinatorRegistryV1,
    LaneCoordinatorReleaseV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    LaneRegistryV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    RouteRegistryV1,
    RouteReleaseV1,
)

_CLOSED_ENUM_TYPES_V1 = {
    EvidenceStatusV1,
    LaneIdV1,
    ProfileStatusV1,
    ReleaseStatusV1,
}


def _require_exact_record_v1(
    value: Any,
    expected_type: type[Any],
    *,
    name: str,
    aggregate_fields: frozenset[str] = frozenset(),
) -> None:
    if type(value) is not expected_type:
        raise TypeError(f"economic profile {name} must have the exact typed value")
    for field in fields(value):
        item = getattr(value, field.name)
        if field.name in aggregate_fields:
            continue
        if isinstance(item, Enum):
            if type(item) not in _CLOSED_ENUM_TYPES_V1:
                raise TypeError(
                    f"economic profile {name}.{field.name} has an unknown enum"
                )
            continue
        if type(item) not in {str, int, bool}:
            raise TypeError(
                f"economic profile {name}.{field.name} must be an exact primitive"
            )


def _require_exact_tuple_v1(
    values: object,
    expected_type: type[Any],
    *,
    name: str,
) -> tuple[Any, ...]:
    if type(values) is not tuple:
        raise TypeError(f"economic profile {name} must be an exact tuple")
    if any(type(value) is not expected_type for value in values):
        raise TypeError(f"economic profile {name} contains an invalid typed value")
    return values


def _snapshot_lane_release_v1(release: LaneModuleReleaseV1) -> LaneModuleReleaseV1:
    tuple_fields = frozenset(
        {
            "command_variants",
            "terminal_command_variants",
            "evidence_statuses",
        }
    )
    _require_exact_record_v1(
        release,
        LaneModuleReleaseV1,
        name="lane release",
        aggregate_fields=tuple_fields,
    )
    return replace(
        release,
        command_variants=tuple(
            _require_exact_tuple_v1(
                release.command_variants,
                str,
                name="lane command variants",
            )
        ),
        terminal_command_variants=tuple(
            _require_exact_tuple_v1(
                release.terminal_command_variants,
                str,
                name="lane terminal command variants",
            )
        ),
        evidence_statuses=tuple(
            _require_exact_tuple_v1(
                release.evidence_statuses,
                EvidenceStatusV1,
                name="lane evidence statuses",
            )
        ),
    )


def _snapshot_lane_registry_v1(registry: LaneRegistryV1) -> LaneRegistryV1:
    _require_exact_record_v1(
        registry,
        LaneRegistryV1,
        name="lane registry",
        aggregate_fields=frozenset({"releases"}),
    )
    return LaneRegistryV1(
        tuple(
            _snapshot_lane_release_v1(release)
            for release in _require_exact_tuple_v1(
                registry.releases,
                LaneModuleReleaseV1,
                name="lane registry releases",
            )
        )
    )


def _snapshot_coordinator_release_v1(
    release: LaneCoordinatorReleaseV1,
) -> LaneCoordinatorReleaseV1:
    _require_exact_record_v1(
        release,
        LaneCoordinatorReleaseV1,
        name="coordinator release",
        aggregate_fields=frozenset({"evidence_statuses"}),
    )
    return replace(
        release,
        evidence_statuses=tuple(
            _require_exact_tuple_v1(
                release.evidence_statuses,
                EvidenceStatusV1,
                name="coordinator evidence statuses",
            )
        ),
    )


def _snapshot_coordinator_registry_v1(
    registry: LaneCoordinatorRegistryV1,
) -> LaneCoordinatorRegistryV1:
    _require_exact_record_v1(
        registry,
        LaneCoordinatorRegistryV1,
        name="coordinator registry",
        aggregate_fields=frozenset({"releases"}),
    )
    return LaneCoordinatorRegistryV1(
        tuple(
            _snapshot_coordinator_release_v1(release)
            for release in _require_exact_tuple_v1(
                registry.releases,
                LaneCoordinatorReleaseV1,
                name="coordinator registry releases",
            )
        )
    )


def _snapshot_route_release_v1(release: RouteReleaseV1) -> RouteReleaseV1:
    tuple_fields = frozenset(
        {
            "ordered_lanes",
            "module_release_ids",
            "dependency_roles",
            "port_schema_roots",
            "evidence_statuses",
        }
    )
    _require_exact_record_v1(
        release,
        RouteReleaseV1,
        name="route release",
        aggregate_fields=tuple_fields,
    )
    return replace(
        release,
        ordered_lanes=tuple(
            _require_exact_tuple_v1(
                release.ordered_lanes,
                LaneIdV1,
                name="route ordered lanes",
            )
        ),
        module_release_ids=tuple(
            _require_exact_tuple_v1(
                release.module_release_ids,
                str,
                name="route module release ids",
            )
        ),
        dependency_roles=tuple(
            _require_exact_tuple_v1(
                release.dependency_roles,
                str,
                name="route dependency roles",
            )
        ),
        port_schema_roots=tuple(
            _require_exact_tuple_v1(
                release.port_schema_roots,
                str,
                name="route port schema roots",
            )
        ),
        evidence_statuses=tuple(
            _require_exact_tuple_v1(
                release.evidence_statuses,
                EvidenceStatusV1,
                name="route evidence statuses",
            )
        ),
    )


def _snapshot_route_registry_v1(registry: RouteRegistryV1) -> RouteRegistryV1:
    _require_exact_record_v1(
        registry,
        RouteRegistryV1,
        name="route registry",
        aggregate_fields=frozenset({"routes"}),
    )
    return RouteRegistryV1(
        tuple(
            _snapshot_route_release_v1(route)
            for route in _require_exact_tuple_v1(
                registry.routes,
                RouteReleaseV1,
                name="route registry routes",
            )
        )
    )


def snapshot_economic_profile_v1(
    profile: EconomicProfileSnapshotV1,
) -> EconomicProfileSnapshotV1:
    """Copy and revalidate the complete content-derived profile graph."""

    registry_fields = frozenset(
        {
            "lane_registry",
            "lane_coordinator_registry",
            "route_registry",
        }
    )
    _require_exact_record_v1(
        profile,
        EconomicProfileSnapshotV1,
        name="snapshot",
        aggregate_fields=registry_fields,
    )
    return replace(
        profile,
        lane_registry=_snapshot_lane_registry_v1(profile.lane_registry),
        lane_coordinator_registry=_snapshot_coordinator_registry_v1(
            profile.lane_coordinator_registry
        ),
        route_registry=_snapshot_route_registry_v1(profile.route_registry),
    )


__all__ = ["snapshot_economic_profile_v1"]
