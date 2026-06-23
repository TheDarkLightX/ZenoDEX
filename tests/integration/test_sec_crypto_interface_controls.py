from __future__ import annotations

from pathlib import Path

from tools.covered_ui_lint import scan_paths


ROOT = Path(__file__).resolve().parents[2]
CONTROL_DOC = ROOT / "docs" / "SEC_CRYPTO_INTERFACE_CONTROLS.md"
UI_LINT_PATHS = (
    "tools/dex-ui/src",
    "tools/dex-ui/README.md",
    "tools/dex-ui/index.html",
)


def test_sec_crypto_interface_controls_doc_records_source_and_release_gate() -> None:
    text = CONTROL_DOC.read_text(encoding="utf-8")

    assert "retrieved 2026-04-27" in text
    assert "2026-04-13" in text
    assert "https://www.sec.gov/newsroom/speeches-statements/" in text
    assert "SelfCustody" in text
    assert "NoDiscretion" in text
    assert "NoCustody" in text
    assert "No investment recommendations" in text
    assert "python3 tools/covered_ui_lint.py --strict" in text
    assert "not legal advice" in text


def test_ui_source_avoids_broker_like_recommendation_phrasing() -> None:
    _files, findings = scan_paths(UI_LINT_PATHS)
    assert not findings, "\n".join(
        f"{finding.path}:{finding.line}: {finding.rule_id}: {finding.text}"
        for finding in findings
    )
