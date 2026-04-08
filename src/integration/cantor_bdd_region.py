from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Iterable, Iterator, Sequence

from .cantor_prefix_algebra import CantorPrefixRegion, Prefix, _coerce_bit, partition_ok
from .cantor_region_morphisms import project_coordinates, pullback_coordinates
from .cantor_region_products import enumerate_depth_words, product_region
from .region_ba import RegionBA


BDDNode = int | tuple[int, "BDDNode", "BDDNode"]
Word = tuple[int, ...]


def _coerce_depth(depth: int) -> int:
    if not isinstance(depth, int) or isinstance(depth, bool) or depth < 0:
        raise ValueError("depth must be a non-negative int")
    return int(depth)


def _mk_node(level: int, left: BDDNode, right: BDDNode) -> BDDNode:
    return left if left == right else (int(level), left, right)


def _normalize_node(node: BDDNode) -> BDDNode:
    if node in (0, 1):
        return int(node)
    if not (isinstance(node, tuple) and len(node) == 3):
        raise ValueError("BDD nodes must be 0, 1, or (level, left, right) tuples")
    level, left, right = node
    if not isinstance(level, int) or isinstance(level, bool) or level < 0:
        raise ValueError("BDD node levels must be non-negative ints")
    left_norm = _normalize_node(left)
    right_norm = _normalize_node(right)
    return _mk_node(level, left_norm, right_norm)


def _build_node_from_words(words: tuple[Word, ...], *, level: int, depth: int) -> BDDNode:
    if not words:
        return 0
    if level == depth:
        return 1
    left_words = tuple(word for word in words if word[level] == 0)
    right_words = tuple(word for word in words if word[level] == 1)
    left = _build_node_from_words(left_words, level=level + 1, depth=depth)
    right = _build_node_from_words(right_words, level=level + 1, depth=depth)
    return _mk_node(level, left, right)


def _enumerate_node_words(node: BDDNode, *, depth: int, level: int = 0, prefix: Prefix = ()) -> tuple[Word, ...]:
    if node == 0:
        return ()
    if node == 1:
        suffix_len = depth - len(prefix)
        return tuple(prefix + tuple(int(bit) for bit in suffix) for suffix in product((0, 1), repeat=suffix_len))

    node_level, left, right = node
    if node_level < level:
        raise ValueError("BDD node levels must increase along every branch")
    if level < node_level:
        return _enumerate_node_words(node, depth=depth, level=level + 1, prefix=prefix + (0,)) + _enumerate_node_words(
            node,
            depth=depth,
            level=level + 1,
            prefix=prefix + (1,),
        )
    if len(prefix) >= depth:
        raise ValueError("BDD node exceeds declared depth")
    return _enumerate_node_words(left, depth=depth, level=level + 1, prefix=prefix + (0,)) + _enumerate_node_words(
        right,
        depth=depth,
        level=level + 1,
        prefix=prefix + (1,),
    )


def _prefix_region_from_node(*, depth: int, node: BDDNode) -> CantorPrefixRegion:
    return CantorPrefixRegion(_enumerate_node_words(node, depth=depth))


def _canonicalize(depth: int, node: BDDNode) -> tuple[int, BDDNode]:
    validated_depth = _coerce_depth(depth)
    normalized_node = _normalize_node(node)
    prefix_region = _prefix_region_from_node(depth=validated_depth, node=normalized_node)
    canonical_depth = prefix_region.depth
    canonical_words = enumerate_depth_words(prefix_region, canonical_depth)
    return canonical_depth, _build_node_from_words(canonical_words, level=0, depth=canonical_depth)


@dataclass(frozen=True)
class CantorBDDRegion:
    depth: int = 0
    node: BDDNode = 0

    def __post_init__(self) -> None:
        depth, node = _canonicalize(self.depth, self.node)
        object.__setattr__(self, "depth", depth)
        object.__setattr__(self, "node", node)

    @classmethod
    def empty(cls) -> "CantorBDDRegion":
        return cls(0, 0)

    @classmethod
    def top(cls) -> "CantorBDDRegion":
        return cls(0, 1)

    @classmethod
    def from_prefix_region(cls, region: CantorPrefixRegion) -> "CantorBDDRegion":
        words = enumerate_depth_words(region, region.depth)
        return cls.from_depth_words(words)

    @classmethod
    def from_prefix(cls, prefix: Sequence[int | bool]) -> "CantorBDDRegion":
        return cls.from_prefix_region(CantorPrefixRegion.from_prefix(prefix))

    @classmethod
    def from_strings(cls, prefixes: Iterable[str]) -> "CantorBDDRegion":
        return cls.from_prefix_region(CantorPrefixRegion.from_strings(prefixes))

    @classmethod
    def from_depth_words(cls, words: Iterable[Word]) -> "CantorBDDRegion":
        normalized = tuple(tuple(_coerce_bit(bit) for bit in word) for word in words)
        if not normalized:
            return cls.empty()
        depth = len(normalized[0])
        if any(len(word) != depth for word in normalized):
            raise ValueError("all words must have the same length")
        deduped = tuple(sorted(set(normalized)))
        return cls(depth, _build_node_from_words(deduped, level=0, depth=depth))

    @classmethod
    def depth_partition(cls, depth: int) -> tuple["CantorBDDRegion", ...]:
        validated_depth = _coerce_depth(depth)
        return tuple(cls.from_prefix(bits) for bits in product((0, 1), repeat=validated_depth))

    def _as_prefix_region(self) -> CantorPrefixRegion:
        return _prefix_region_from_node(depth=self.depth, node=self.node)

    def is_empty(self) -> bool:
        return self.node == 0

    def is_top(self) -> bool:
        return self.node == 1 and self.depth == 0

    def to_strings(self) -> tuple[str, ...]:
        return self._as_prefix_region().to_strings()

    def iter_prefixes(self) -> Iterator[Prefix]:
        return self._as_prefix_region().iter_prefixes()

    def covers_word(self, word: Sequence[int | bool]) -> bool:
        return self._as_prefix_region().covers_word(word)

    def __or__(self, other: "CantorBDDRegion") -> "CantorBDDRegion":
        return CantorBDDRegion.from_prefix_region(self._as_prefix_region() | other._as_prefix_region())

    def __and__(self, other: "CantorBDDRegion") -> "CantorBDDRegion":
        return CantorBDDRegion.from_prefix_region(self._as_prefix_region() & other._as_prefix_region())

    def __invert__(self) -> "CantorBDDRegion":
        return CantorBDDRegion.from_prefix_region(~self._as_prefix_region())

    def __le__(self, other: "CantorBDDRegion") -> bool:
        return bool(self._as_prefix_region() <= other._as_prefix_region())


CantorBDDRegionBA = RegionBA[CantorBDDRegion]


def _bdd_partition_ok(parts: Sequence[CantorBDDRegion]) -> bool:
    return partition_ok(tuple(part._as_prefix_region() for part in parts))


def _bdd_describe(region: CantorBDDRegion) -> tuple[str, ...]:
    return region.to_strings()


def _bdd_cube_count(region: CantorBDDRegion, depth: int) -> int:
    return len(enumerate_depth_words(region._as_prefix_region(), _coerce_depth(depth)))


def _bdd_product(left: CantorBDDRegion, left_depth: int, right: CantorBDDRegion, right_depth: int) -> CantorBDDRegion:
    return CantorBDDRegion.from_prefix_region(
        product_region(
            left._as_prefix_region(),
            left_depth=left_depth,
            right=right._as_prefix_region(),
            right_depth=right_depth,
        )
    )


def _bdd_project(region: CantorBDDRegion, source_depth: int, coordinates: Sequence[int]) -> CantorBDDRegion:
    return CantorBDDRegion.from_prefix_region(
        project_coordinates(
            region._as_prefix_region(),
            source_depth=source_depth,
            coordinates=coordinates,
        )
    )


def _bdd_pullback(region: CantorBDDRegion, target_depth: int, source_depth: int, coordinates: Sequence[int]) -> CantorBDDRegion:
    return CantorBDDRegion.from_prefix_region(
        pullback_coordinates(
            region._as_prefix_region(),
            target_depth=target_depth,
            source_depth=source_depth,
            coordinates=coordinates,
        )
    )


def build_cantor_bdd_region_ba() -> CantorBDDRegionBA:
    return CantorBDDRegionBA(
        name="cantor_reduced_decision_diagram",
        region_type=CantorBDDRegion,
        partition_predicate=_bdd_partition_ok,
        cube_counter=_bdd_cube_count,
        region_describer=_bdd_describe,
        product_builder=_bdd_product,
        coordinate_projector=_bdd_project,
        coordinate_pullback=_bdd_pullback,
    )
