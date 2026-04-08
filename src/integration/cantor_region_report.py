from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping, Sequence

from .cantor_prefix_algebra import CantorPrefixRegion, format_prefix, partition_ok


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
    if not isinstance(depth, int) or isinstance(depth, bool) or depth < 0:
        raise ValueError("depth must be a non-negative int")
    total = 0
    for prefix in region.iter_prefixes():
        if len(prefix) > depth:
            continue
        total += 1 << (depth - len(prefix))
    return total


def region_stats(name: str, region: CantorPrefixRegion, *, depth: int) -> CantorRegionStats:
    return CantorRegionStats(
        name=str(name),
        prefix_count=len(region.prefixes),
        depth=int(depth),
        depth_cube_count=depth_cube_count(region, depth),
        prefixes=tuple(format_prefix(prefix) for prefix in region.iter_prefixes()),
    )


def build_cantor_region_report(
    *,
    depth: int,
    regions: Mapping[str, CantorPrefixRegion],
    partition: Sequence[str] = (),
    refinements: Sequence[tuple[str, str]] = (),
    disjoint_pairs: Sequence[tuple[str, str]] = (),
) -> CantorRegionReport:
    if not regions:
        raise ValueError("regions must be non-empty")

    normalized_regions = {str(name): region for name, region in regions.items()}
    stats = tuple(region_stats(name, region, depth=depth) for name, region in normalized_regions.items())

    partition_names = tuple(str(name) for name in partition)
    partition_total = False
    if partition_names:
        partition_total = partition_ok(tuple(normalized_regions[name] for name in partition_names))

    refinement_relations = tuple(
        CantorRegionRelation(left=str(left), right=str(right), holds=normalized_regions[left] <= normalized_regions[right], kind="refines")
        for left, right in refinements
    )
    disjoint_relations = tuple(
        CantorRegionRelation(
            left=str(left),
            right=str(right),
            holds=(normalized_regions[left] & normalized_regions[right]).is_empty(),
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
