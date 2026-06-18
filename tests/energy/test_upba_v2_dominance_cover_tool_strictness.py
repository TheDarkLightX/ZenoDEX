from __future__ import annotations

from tools.check_upba_v2_dominance_cover import _summarize_reports


def _report(**overrides: object) -> dict[str, object]:
    report: dict[str, object] = {
        "ok": True,
        "dominance_cover_ok": True,
        "structural_verify_ok": True,
        "uncovered_full_count": 0,
    }
    report.update(overrides)
    return report


def test_dominance_cover_summary_counts_only_literal_true() -> None:
    summary = _summarize_reports(
        [
            _report(ok=True, dominance_cover_ok=True, structural_verify_ok=True),
            _report(ok="true", dominance_cover_ok="true", structural_verify_ok=1),
            _report(ok=1, dominance_cover_ok=True, structural_verify_ok=True),
        ]
    )

    assert summary["count"] == 3
    assert summary["ok_count"] == 1
    assert summary["failed_count"] == 2
    assert summary["dominance_cover_ok_count"] == 2
    assert summary["structural_verify_ok_count"] == 2
