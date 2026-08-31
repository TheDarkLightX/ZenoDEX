from __future__ import annotations

import json

from tools.render_global_settlement_abi_v2_asset_transfer_golden import (
    FIXTURE_PATH_V2,
    FROZEN_V1_GOLDEN_SHA256,
    build_vectors_v2,
    render_vectors_v2,
)


def test_committed_v2_fixture_matches_typed_python_renderer() -> None:
    fixture_text = FIXTURE_PATH_V2.read_text(encoding="utf-8")

    assert fixture_text == render_vectors_v2()
    assert json.loads(fixture_text) == build_vectors_v2()


def test_v2_fixture_retains_the_frozen_v1_subject_hash() -> None:
    fixture = build_vectors_v2()

    assert fixture["authority"] == "NONE"
    assert fixture["frozen_v1_golden_sha256"] == FROZEN_V1_GOLDEN_SHA256
