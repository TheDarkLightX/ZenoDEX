from __future__ import annotations

import importlib.util
from itertools import product

import pytest

from src.integration.cantor_prefix_algebra import (
    CantorPrefixRegion,
    format_prefix,
    parse_prefix,
    partition_ok,
)

if importlib.util.find_spec("hypothesis") is None:  # pragma: no cover
    pytest.skip("hypothesis not installed", allow_module_level=True)

import hypothesis.strategies as st
from hypothesis import given, settings


@st.composite
def _regions(draw) -> CantorPrefixRegion:
    prefixes = draw(st.lists(st.text(alphabet="01", min_size=0, max_size=5), min_size=0, max_size=8))
    return CantorPrefixRegion.from_strings(prefixes)


@st.composite
def _three_regions(draw) -> tuple[CantorPrefixRegion, CantorPrefixRegion, CantorPrefixRegion]:
    return draw(_regions()), draw(_regions()), draw(_regions())


def _words(depth: int) -> tuple[tuple[int, ...], ...]:
    return tuple(tuple(bits) for bits in product((0, 1), repeat=depth))


def _same_denotation(left: CantorPrefixRegion, right: CantorPrefixRegion) -> bool:
    depth = max(left.depth, right.depth)
    return all(left.covers_word(word) == right.covers_word(word) for word in _words(depth))


def test_parse_and_format_prefix_round_trip() -> None:
    assert parse_prefix("*") == ()
    assert parse_prefix("010*") == (0, 1, 0)
    assert format_prefix(()) == "*"
    assert format_prefix((1, 0, 1)) == "101*"


def test_normalization_removes_descendants_and_merges_siblings() -> None:
    region = CantorPrefixRegion.from_strings(["0", "00", "01", "10", "11"])
    assert region.to_strings() == ("*",)


def test_complement_of_basic_cylinder_is_other_half() -> None:
    region = CantorPrefixRegion.from_strings(["0"])
    assert (~region).to_strings() == ("1*",)


def test_meet_keeps_longer_prefix_when_cylinders_overlap() -> None:
    left = CantorPrefixRegion.from_strings(["0"])
    right = CantorPrefixRegion.from_strings(["01"])
    assert (left & right).to_strings() == ("01*",)


def test_depth_partition_is_total_and_disjoint() -> None:
    parts = CantorPrefixRegion.depth_partition(3)
    assert len(parts) == 8
    assert partition_ok(parts)


def test_witness_refinement_matches_prefix_refinement() -> None:
    coarse = CantorPrefixRegion.from_prefix((1, 0))
    fine = CantorPrefixRegion.from_prefix((1, 0, 1, 1))

    assert fine.refines(coarse)
    assert not coarse.refines(fine)


@given(region=_regions())
@settings(max_examples=100, deadline=None)
def test_normalization_is_idempotent(region: CantorPrefixRegion) -> None:
    assert CantorPrefixRegion(region.prefixes) == region


@given(region=_regions())
@settings(max_examples=100, deadline=None)
def test_complement_is_involutive(region: CantorPrefixRegion) -> None:
    assert ~~region == region


@given(region=_regions())
@settings(max_examples=100, deadline=None)
def test_region_and_complement_partition_space(region: CantorPrefixRegion) -> None:
    assert (region & ~region).is_empty()
    assert (region | ~region).is_top()


@given(left=_regions(), right=_regions())
@settings(max_examples=100, deadline=None)
def test_de_morgan_law(left: CantorPrefixRegion, right: CantorPrefixRegion) -> None:
    assert ~(left | right) == ((~left) & (~right))


@given(case=_three_regions())
@settings(max_examples=80, deadline=None)
def test_distributivity(case: tuple[CantorPrefixRegion, CantorPrefixRegion, CantorPrefixRegion]) -> None:
    left, mid, right = case
    assert left & (mid | right) == ((left & mid) | (left & right))


@given(left=_regions(), right=_regions())
@settings(max_examples=100, deadline=None)
def test_inclusion_matches_meet_characterization(left: CantorPrefixRegion, right: CantorPrefixRegion) -> None:
    assert (left <= right) == ((left & right) == left)


@given(left=_regions(), right=_regions())
@settings(max_examples=80, deadline=None)
def test_equality_matches_finite_word_denotation(left: CantorPrefixRegion, right: CantorPrefixRegion) -> None:
    assert (left == right) == _same_denotation(left, right)
