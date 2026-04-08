from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Sequence

from .cantor_prefix_algebra import CantorPrefixRegion
from .cantor_region_morphisms import project_coordinates, pullback_coordinates
from .cantor_region_products import product_region
from .cantor_region_report import CantorRegionStats, depth_cube_count, region_stats


def _stats_payload(stats: CantorRegionStats) -> dict[str, object]:
    return {
        "name": stats.name,
        "prefix_count": stats.prefix_count,
        "depth": stats.depth,
        "depth_cube_count": stats.depth_cube_count,
        "prefixes": list(stats.prefixes),
    }


@dataclass(frozen=True)
class CantorRegionProjectionReceipt:
    name: str
    source_depth: int
    target_depth: int
    coordinates: tuple[int, ...]
    source: CantorRegionStats
    projected: CantorRegionStats
    lifted_projection: CantorRegionStats
    source_refines_lifted_projection: bool
    project_after_lift_recovers_projection: bool
    projected_cube_bound_holds: bool
    lift_cube_factor: int
    lift_cube_count_matches_factor: bool

    def to_dict(self) -> dict[str, object]:
        return {
            "name": self.name,
            "source_depth": self.source_depth,
            "target_depth": self.target_depth,
            "coordinates": list(self.coordinates),
            "source": _stats_payload(self.source),
            "projected": _stats_payload(self.projected),
            "lifted_projection": _stats_payload(self.lifted_projection),
            "source_refines_lifted_projection": self.source_refines_lifted_projection,
            "project_after_lift_recovers_projection": self.project_after_lift_recovers_projection,
            "projected_cube_bound_holds": self.projected_cube_bound_holds,
            "lift_cube_factor": self.lift_cube_factor,
            "lift_cube_count_matches_factor": self.lift_cube_count_matches_factor,
        }


@dataclass(frozen=True)
class CantorRegionProductProjectionReceipt:
    product_name: str
    product: CantorRegionStats
    left_projection: CantorRegionProjectionReceipt
    right_projection: CantorRegionProjectionReceipt
    product_cube_count_matches_factor_counts: bool

    def to_dict(self) -> dict[str, object]:
        return {
            "product_name": self.product_name,
            "product": _stats_payload(self.product),
            "left_projection": self.left_projection.to_dict(),
            "right_projection": self.right_projection.to_dict(),
            "product_cube_count_matches_factor_counts": self.product_cube_count_matches_factor_counts,
        }


def build_cantor_region_projection_receipt(
    *,
    name: str,
    source_region: CantorPrefixRegion,
    source_depth: int,
    coordinates: Sequence[int],
) -> CantorRegionProjectionReceipt:
    projected = project_coordinates(source_region, source_depth=source_depth, coordinates=coordinates)
    target_depth = len(tuple(int(coord) for coord in coordinates))
    lifted_projection = pullback_coordinates(
        projected,
        target_depth=target_depth,
        source_depth=source_depth,
        coordinates=coordinates,
    )
    lift_cube_factor = 1 << (source_depth - target_depth)
    projected_count = depth_cube_count(projected, target_depth)

    return CantorRegionProjectionReceipt(
        name=str(name),
        source_depth=int(source_depth),
        target_depth=target_depth,
        coordinates=tuple(int(coord) for coord in coordinates),
        source=region_stats(f"{name}_source", source_region, depth=source_depth),
        projected=region_stats(f"{name}_projected", projected, depth=target_depth),
        lifted_projection=region_stats(f"{name}_lifted_projection", lifted_projection, depth=source_depth),
        source_refines_lifted_projection=source_region <= lifted_projection,
        project_after_lift_recovers_projection=(
            project_coordinates(lifted_projection, source_depth=source_depth, coordinates=coordinates) == projected
        ),
        projected_cube_bound_holds=projected_count <= depth_cube_count(source_region, source_depth),
        lift_cube_factor=lift_cube_factor,
        lift_cube_count_matches_factor=(
            depth_cube_count(lifted_projection, source_depth) == projected_count * lift_cube_factor
        ),
    )


def build_cantor_region_product_projection_receipt(
    *,
    product_name: str,
    left_name: str,
    left_region: CantorPrefixRegion,
    left_depth: int,
    right_name: str,
    right_region: CantorPrefixRegion,
    right_depth: int,
) -> CantorRegionProductProjectionReceipt:
    product = product_region(left_region, left_depth=left_depth, right=right_region, right_depth=right_depth)
    product_depth = left_depth + right_depth
    left_projection = build_cantor_region_projection_receipt(
        name=left_name,
        source_region=product,
        source_depth=product_depth,
        coordinates=tuple(range(left_depth)),
    )
    right_projection = build_cantor_region_projection_receipt(
        name=right_name,
        source_region=product,
        source_depth=product_depth,
        coordinates=tuple(range(left_depth, product_depth)),
    )
    product_stats = region_stats(str(product_name), product, depth=product_depth)

    return CantorRegionProductProjectionReceipt(
        product_name=str(product_name),
        product=product_stats,
        left_projection=left_projection,
        right_projection=right_projection,
        product_cube_count_matches_factor_counts=(
            product_stats.depth_cube_count
            == left_projection.projected.depth_cube_count * right_projection.projected.depth_cube_count
        ),
    )
