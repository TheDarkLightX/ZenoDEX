from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Generic, Protocol, Self, Sequence, TypeVar, runtime_checkable

from .cantor_prefix_algebra import CantorPrefixRegion, partition_ok
from .cantor_region_morphisms import project_coordinates, pullback_coordinates
from .cantor_region_products import product_region
from .cantor_region_report import depth_cube_count


@runtime_checkable
class RegionElement(Protocol):
    @classmethod
    def empty(cls) -> Self: ...

    @classmethod
    def top(cls) -> Self: ...

    def is_empty(self) -> bool: ...

    def is_top(self) -> bool: ...

    def __or__(self, other: Self) -> Self: ...

    def __and__(self, other: Self) -> Self: ...

    def __invert__(self) -> Self: ...

    def __le__(self, other: Self) -> bool: ...


R = TypeVar("R", bound=RegionElement)


@dataclass(frozen=True)
class RegionBA(Generic[R]):
    name: str
    region_type: type[R]
    partition_predicate: Callable[[Sequence[R]], bool]
    cube_counter: Callable[[R, int], int]
    product_builder: Callable[[R, int, R, int], R]
    coordinate_projector: Callable[[R, int, Sequence[int]], R]
    coordinate_pullback: Callable[[R, int, int, Sequence[int]], R]

    def zero(self) -> R:
        return self.region_type.empty()

    def one(self) -> R:
        return self.region_type.top()

    def join(self, left: R, right: R) -> R:
        return left | right

    def meet(self, left: R, right: R) -> R:
        return left & right

    def complement(self, region: R) -> R:
        return ~region

    def leq(self, left: R, right: R) -> bool:
        return bool(left <= right)

    def disjoint(self, left: R, right: R) -> bool:
        return self.meet(left, right).is_empty()

    def partition_ok(self, parts: Sequence[R]) -> bool:
        return bool(self.partition_predicate(parts))

    def cube_count(self, region: R, *, depth: int) -> int:
        return int(self.cube_counter(region, int(depth)))

    def product(self, left: R, *, left_depth: int, right: R, right_depth: int) -> R:
        return self.product_builder(left, int(left_depth), right, int(right_depth))

    def project(self, region: R, *, source_depth: int, coordinates: Sequence[int]) -> R:
        return self.coordinate_projector(region, int(source_depth), coordinates)

    def pullback(
        self,
        region: R,
        *,
        target_depth: int,
        source_depth: int,
        coordinates: Sequence[int],
    ) -> R:
        return self.coordinate_pullback(region, int(target_depth), int(source_depth), coordinates)


CantorRegionBA = RegionBA[CantorPrefixRegion]


def build_cantor_region_ba() -> CantorRegionBA:
    return CantorRegionBA(
        name="cantor_prefix_antichain",
        region_type=CantorPrefixRegion,
        partition_predicate=partition_ok,
        cube_counter=depth_cube_count,
        product_builder=lambda left, left_depth, right, right_depth: product_region(
            left,
            left_depth=left_depth,
            right=right,
            right_depth=right_depth,
        ),
        coordinate_projector=lambda region, source_depth, coordinates: project_coordinates(
            region,
            source_depth=source_depth,
            coordinates=coordinates,
        ),
        coordinate_pullback=lambda region, target_depth, source_depth, coordinates: pullback_coordinates(
            region,
            target_depth=target_depth,
            source_depth=source_depth,
            coordinates=coordinates,
        ),
    )
