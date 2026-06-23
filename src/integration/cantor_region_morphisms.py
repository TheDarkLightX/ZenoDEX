from __future__ import annotations

from itertools import product
from typing import Sequence

from .cantor_prefix_algebra import CantorPrefixRegion
from .cantor_region_products import enumerate_depth_words, region_from_depth_words


def _normalize_coordinates(coordinates: Sequence[int], *, source_depth: int) -> tuple[int, ...]:
    coords = tuple(int(coord) for coord in coordinates)
    if len(set(coords)) != len(coords):
        raise ValueError("coordinates must be unique")
    if any(coord < 0 or coord >= source_depth for coord in coords):
        raise ValueError("coordinates out of range for source_depth")
    return coords


def project_coordinates(
    region: CantorPrefixRegion,
    *,
    source_depth: int,
    coordinates: Sequence[int],
) -> CantorPrefixRegion:
    coords = _normalize_coordinates(coordinates, source_depth=source_depth)
    words = enumerate_depth_words(region, source_depth)
    return region_from_depth_words(tuple(tuple(word[index] for index in coords) for word in words))


def pullback_coordinates(
    region: CantorPrefixRegion,
    *,
    target_depth: int,
    source_depth: int,
    coordinates: Sequence[int],
) -> CantorPrefixRegion:
    coords = _normalize_coordinates(coordinates, source_depth=source_depth)
    if len(coords) != target_depth:
        raise ValueError("target_depth must equal len(coordinates)")

    coarse_words = enumerate_depth_words(region, target_depth)
    other_positions = tuple(index for index in range(source_depth) if index not in coords)
    lifted_words: list[tuple[int, ...]] = []
    for coarse_word in coarse_words:
        for filler in product((0, 1), repeat=len(other_positions)):
            full = [0] * source_depth
            for index, bit in zip(coords, coarse_word):
                full[index] = int(bit)
            for index, bit in zip(other_positions, filler):
                full[index] = int(bit)
            lifted_words.append(tuple(full))
    return region_from_depth_words(tuple(lifted_words))
