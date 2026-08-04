from __future__ import annotations

from pathlib import Path

import pytest

from tools import check_dependency_pinning_status as checker
from tools.check_dependency_pinning_status import run_check


def test_dependency_pinning_status_ratchet_accepts_current_manifest() -> None:
    result = run_check()

    assert result["ok"] is True
    assert result["schema"] == "zenodex.dependency_pinning_status_check.v1"
    assert result["known_unpinned_count"] == 21
    assert result["lock_artifact_hash_count"] == 8
    assert result["errors"] == []


def test_dependency_pinning_status_scans_included_requirement_files(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    (tmp_path / "requirements.txt").write_text("-r nested/extra.txt\nroot-package==1.0\n", encoding="utf-8")
    (tmp_path / "nested").mkdir()
    (tmp_path / "nested" / "extra.txt").write_text("hidden-package>=0\n", encoding="utf-8")
    monkeypatch.setattr(checker, "ROOT", tmp_path)

    assert checker._actual_unpinned(["requirements.txt"]) == ["nested/extra.txt:hidden-package>=0"]


def test_dependency_pinning_status_scans_long_form_includes(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    (tmp_path / "requirements.txt").write_text("--requirement=nested/extra.txt\n", encoding="utf-8")
    (tmp_path / "nested").mkdir()
    (tmp_path / "nested" / "extra.txt").write_text("hidden-package>=0\n", encoding="utf-8")
    monkeypatch.setattr(checker, "ROOT", tmp_path)

    assert checker._actual_unpinned(["requirements.txt"]) == ["nested/extra.txt:hidden-package>=0"]


def test_dependency_pinning_status_rejects_includes_outside_repository(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    (tmp_path / "requirements.txt").write_text("-r ../outside.txt\n", encoding="utf-8")
    monkeypatch.setattr(checker, "ROOT", tmp_path)

    with pytest.raises(ValueError, match="escapes repository"):
        checker._actual_unpinned(["requirements.txt"])
