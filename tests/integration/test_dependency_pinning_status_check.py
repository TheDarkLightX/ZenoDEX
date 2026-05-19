from __future__ import annotations

from tools.check_dependency_pinning_status import run_check


def test_dependency_pinning_status_ratchet_accepts_current_manifest() -> None:
    result = run_check()

    assert result["ok"] is True
    assert result["schema"] == "zenodex.dependency_pinning_status_check.v1"
    assert result["known_unpinned_count"] == 17
    assert result["lock_artifact_hash_count"] == 8
    assert result["errors"] == []
