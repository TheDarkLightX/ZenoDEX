from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Generic, Protocol, Self, Sequence, TypeVar, runtime_checkable

from .cantor_prefix_algebra import CantorPrefixRegion, format_prefix, partition_ok
from .cantor_region_morphisms import project_coordinates, pullback_coordinates
from .cantor_region_products import product_region


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
    prefix_loader: Callable[[Sequence[str]], R]
    partition_predicate: Callable[[Sequence[R]], bool]
    cube_counter: Callable[[R, int], int]
    region_describer: Callable[[R], tuple[str, ...]]
    product_builder: Callable[[R, int, R, int], R]
    coordinate_projector: Callable[[R, int, Sequence[int]], R]
    coordinate_pullback: Callable[[R, int, int, Sequence[int]], R]

    def zero(self) -> R:
        return self.region_type.empty()

    def one(self) -> R:
        return self.region_type.top()

    def from_strings(self, prefixes: Sequence[str]) -> R:
        return self.prefix_loader(tuple(str(prefix) for prefix in prefixes))

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

    def describe(self, region: R) -> tuple[str, ...]:
        return tuple(str(part) for part in self.region_describer(region))

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


def _cantor_depth_cube_count(region: CantorPrefixRegion, depth: int) -> int:
    if not isinstance(depth, int) or isinstance(depth, bool) or depth < 0:
        raise ValueError("depth must be a non-negative int")
    total = 0
    for prefix in region.iter_prefixes():
        if len(prefix) > depth:
            continue
        total += 1 << (depth - len(prefix))
    return total


def _cantor_describe(region: CantorPrefixRegion) -> tuple[str, ...]:
    return tuple(format_prefix(prefix) for prefix in region.iter_prefixes())


def build_cantor_region_ba() -> CantorRegionBA:
    return CantorRegionBA(
        name="cantor_prefix_antichain",
        region_type=CantorPrefixRegion,
        prefix_loader=lambda prefixes: CantorPrefixRegion.from_strings(prefixes),
        partition_predicate=partition_ok,
        cube_counter=_cantor_depth_cube_count,
        region_describer=_cantor_describe,
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
