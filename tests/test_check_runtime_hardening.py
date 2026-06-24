from __future__ import annotations

from pathlib import Path

from tools.check_runtime_hardening import audit_runtime_hardening


def _write(path: Path, source: str) -> Path:
    path.write_text(source.strip() + "\n", encoding="utf-8")
    return path


def test_runtime_hardening_accepts_explicit_fail_closed_handler(tmp_path: Path) -> None:
    source = _write(
        tmp_path / "safe.py",
        """
        def parse(value):
            try:
                return int(value)
            except Exception as exc:
                return {"ok": False, "error": type(exc).__name__}
        """,
    )

    report = audit_runtime_hardening(tmp_path, (source,))

    assert report["ok"] is True
    assert report["findings"] == []


def test_runtime_hardening_rejects_runtime_assert(tmp_path: Path) -> None:
    source = _write(
        tmp_path / "unsafe_assert.py",
        """
        def validate(value):
            assert value > 0
            return value
        """,
    )

    report = audit_runtime_hardening(tmp_path, (source,))

    assert report["ok"] is False
    assert report["findings"] == [
        {
            "code": "runtime_assert",
            "path": "unsafe_assert.py",
            "line": 2,
            "function": "validate",
            "detail": "runtime assert is stripped by python -O",
        }
    ]


def test_runtime_hardening_rejects_broad_except_pass(tmp_path: Path) -> None:
    source = _write(
        tmp_path / "unsafe_pass.py",
        """
        def maybe(value):
            try:
                return int(value)
            except Exception:
                pass
        """,
    )

    report = audit_runtime_hardening(tmp_path, (source,))

    assert report["ok"] is False
    assert report["findings"][0]["code"] == "broad_except_pass"
    assert report["findings"][0]["function"] == "maybe"


def test_runtime_hardening_rejects_broad_except_continue(tmp_path: Path) -> None:
    source = _write(
        tmp_path / "unsafe_continue.py",
        """
        def collect(values):
            out = []
            for value in values:
                try:
                    out.append(int(value))
                except BaseException:
                    continue
            return out
        """,
    )

    report = audit_runtime_hardening(tmp_path, (source,))

    assert report["ok"] is False
    assert report["findings"][0]["code"] == "broad_except_continue"
    assert report["findings"][0]["function"] == "collect"


def test_runtime_hardening_rejects_broad_except_return_none(tmp_path: Path) -> None:
    source = _write(
        tmp_path / "unsafe_return_none.py",
        """
        def maybe(value):
            try:
                return int(value)
            except Exception:
                return None
        """,
    )

    report = audit_runtime_hardening(tmp_path, (source,))

    assert report["ok"] is False
    assert report["findings"][0]["code"] == "broad_except_return_none"
    assert report["findings"][0]["function"] == "maybe"


def test_runtime_hardening_repo_default_passes() -> None:
    root = Path(__file__).resolve().parents[1]

    report = audit_runtime_hardening(root)

    assert report["ok"] is True, report["findings"][:5]
    assert report["files_scanned"] > 0
