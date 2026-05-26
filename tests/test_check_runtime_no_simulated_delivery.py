from __future__ import annotations

from pathlib import Path

from tools.check_runtime_no_simulated_delivery import scan_no_simulated_delivery


def test_runtime_no_simulated_delivery_accepts_default_targets() -> None:
    report = scan_no_simulated_delivery()

    assert report["ok"] is True
    assert report["findings"] == []


def test_runtime_no_simulated_delivery_rejects_fabricated_receipt_marker(tmp_path: Path) -> None:
    bad = tmp_path / "bad_runtime.py"
    bad.write_text('receipt_reference = "local-smtp:share:fake"\n', encoding="utf-8")

    report = scan_no_simulated_delivery([bad])

    assert report["ok"] is False
    assert report["findings"][0]["marker"] == "local-smtp:"
