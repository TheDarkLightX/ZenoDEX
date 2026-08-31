from __future__ import annotations

import json

from tools.render_global_settlement_abi_v2_managed_asset_golden import (
    FIXTURE_PATH_V2,
    build_vectors_v2,
    render_vectors_v2,
)


def test_committed_managed_asset_fixture_matches_typed_python_renderer() -> None:
    fixture_text = FIXTURE_PATH_V2.read_text(encoding="utf-8")

    assert fixture_text == render_vectors_v2()
    assert json.loads(fixture_text) == build_vectors_v2()


def test_managed_asset_fixture_is_research_only_and_covers_issue_and_burn() -> None:
    fixture = build_vectors_v2()

    assert fixture["authority"] == "NONE"
    assert fixture["profile_authentication"] == "SHADOW"
    cases = fixture["cases"]
    assert isinstance(cases, dict)
    assert tuple(cases) == ("burn", "issue")
