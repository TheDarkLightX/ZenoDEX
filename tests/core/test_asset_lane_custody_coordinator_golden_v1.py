"""Replay the Python oracle consumed by the native custody coordinator tests."""

from tools.render_asset_lane_custody_coordinator_v1_golden import FIXTURE, render


def test_custody_coordinator_python_vectors_match_current_reference_sources():
    assert FIXTURE.read_text() == render()
