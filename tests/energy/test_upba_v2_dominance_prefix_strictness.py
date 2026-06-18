from __future__ import annotations

from tools.check_upba_v2_dominance_prefix import _summarize_reports


def _report(**overrides: object) -> dict[str, object]:
    report: dict[str, object] = {
        "ok": True,
        "structural_verify_ok": True,
        "permutation_ok": True,
        "prefix_checked_count": 1,
        "prefix_valid_count": 1,
        "prefix_invalid_count": 0,
        "full_candidate_count": 2,
    }
    report.update(overrides)
    return report


def test_prefix_summary_counts_only_literal_true_as_ok() -> None:
    summary = _summarize_reports(
        [
            _report(ok=True, structural_verify_ok=True, permutation_ok=True),
            _report(ok="true", structural_verify_ok="true", permutation_ok=1),
            _report(ok=1, structural_verify_ok=True, permutation_ok=True),
        ]
    )

    assert summary["count"] == 3
    assert summary["ok_count"] == 1
    assert summary["failed_count"] == 2
    assert summary["structural_verify_ok_count"] == 2
    assert summary["permutation_ok_count"] == 2
