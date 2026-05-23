from __future__ import annotations

from itertools import product

from .cantor_prefix_algebra import CantorPrefixRegion


Word = tuple[int, ...]


def enumerate_depth_words(region: CantorPrefixRegion, depth: int) -> tuple[Word, ...]:
    if not isinstance(depth, int) or isinstance(depth, bool) or depth < 0:
        raise ValueError("depth must be a non-negative int")
    words: list[Word] = []
    for prefix in region.iter_prefixes():
        if len(prefix) > depth:
            continue
        suffix_len = depth - len(prefix)
        for suffix in product((0, 1), repeat=suffix_len):
            words.append(prefix + tuple(int(bit) for bit in suffix))
    return tuple(sorted(words))


def region_from_depth_words(words: tuple[Word, ...]) -> CantorPrefixRegion:
    return CantorPrefixRegion(words)


def product_region(
    left: CantorPrefixRegion,
    *,
    left_depth: int,
    right: CantorPrefixRegion,
    right_depth: int,
) -> CantorPrefixRegion:
    left_words = enumerate_depth_words(left, left_depth)
    right_words = enumerate_depth_words(right, right_depth)
    return region_from_depth_words(
        tuple(left_word + right_word for left_word in left_words for right_word in right_words)
    )


def project_left(
    region: CantorPrefixRegion,
    *,
    left_depth: int,
    right_depth: int,
) -> CantorPrefixRegion:
    words = enumerate_depth_words(region, left_depth + right_depth)
    return region_from_depth_words(tuple(word[:left_depth] for word in words))


def project_right(
    region: CantorPrefixRegion,
    *,
    left_depth: int,
    right_depth: int,
) -> CantorPrefixRegion:
    words = enumerate_depth_words(region, left_depth + right_depth)
    return region_from_depth_words(tuple(word[left_depth:] for word in words))
