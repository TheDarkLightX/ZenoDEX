from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping, Sequence, TypeVar

from .cantor_prefix_algebra import CantorPrefixRegion
from .region_ba import RegionBA, RegionElement, build_cantor_region_ba


R = TypeVar("R", bound=RegionElement)


@dataclass(frozen=True)
class CantorRegionStats:
    name: str
    prefix_count: int
    depth: int
    depth_cube_count: int
    prefixes: tuple[str, ...]


@dataclass(frozen=True)
class CantorRegionRelation:
    left: str
    right: str
    holds: bool
    kind: str


@dataclass(frozen=True)
class CantorRegionReport:
    depth: int
    regions: tuple[CantorRegionStats, ...]
    partition_names: tuple[str, ...]
    partition_total: bool
    refinements: tuple[CantorRegionRelation, ...]
    disjoint_pairs: tuple[CantorRegionRelation, ...]


def depth_cube_count(region: CantorPrefixRegion, depth: int) -> int:
    return build_cantor_region_ba().cube_count(region, depth=depth)


def region_stats(
    name: str,
    region: R,
    *,
    depth: int,
    ba: RegionBA[R] | None = None,
) -> CantorRegionStats:
    algebra = ba or build_cantor_region_ba()
    prefixes = algebra.describe(region)
    return CantorRegionStats(
        name=str(name),
        prefix_count=len(prefixes),
        depth=int(depth),
        depth_cube_count=algebra.cube_count(region, depth=depth),
        prefixes=prefixes,
    )


def build_cantor_region_report(
    *,
    depth: int,
    regions: Mapping[str, R],
    partition: Sequence[str] = (),
    refinements: Sequence[tuple[str, str]] = (),
    disjoint_pairs: Sequence[tuple[str, str]] = (),
    ba: RegionBA[R] | None = None,
) -> CantorRegionReport:
    if not regions:
        raise ValueError("regions must be non-empty")

    algebra = ba or build_cantor_region_ba()
    normalized_regions = {str(name): region for name, region in regions.items()}
    stats = tuple(region_stats(name, region, depth=depth, ba=algebra) for name, region in normalized_regions.items())

    partition_names = tuple(str(name) for name in partition)
    partition_total = False
    if partition_names:
        partition_total = algebra.partition_ok(tuple(normalized_regions[name] for name in partition_names))

    refinement_relations = tuple(
        CantorRegionRelation(
            left=str(left),
            right=str(right),
            holds=algebra.leq(normalized_regions[left], normalized_regions[right]),
            kind="refines",
        )
        for left, right in refinements
    )
    disjoint_relations = tuple(
        CantorRegionRelation(
            left=str(left),
            right=str(right),
            holds=algebra.disjoint(normalized_regions[left], normalized_regions[right]),
            kind="disjoint",
        )
        for left, right in disjoint_pairs
    )

    return CantorRegionReport(
        depth=int(depth),
        regions=stats,
        partition_names=partition_names,
        partition_total=bool(partition_total),
        refinements=refinement_relations,
        disjoint_pairs=disjoint_relations,
    )
