"""Retained Python replay for the corpus consumed by the Rust custody tests."""

from tools.render_asset_lane_custody_v2_golden import FIXTURE, render


def test_python_custody_vectors_and_listed_source_hashes_are_current():
    assert render() == FIXTURE.read_bytes()
