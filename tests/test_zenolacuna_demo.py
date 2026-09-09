"""The demo reports an unavailable native tool without publishing completion."""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

from tools.zenolacuna_demo import main


def test_demo_nonexecutable_tau_is_typed_rejection_without_summary(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str],
) -> None:
    binary = tmp_path / "tau"
    binary.write_text("not an executable", encoding="utf-8")
    output = tmp_path / "demo"
    monkeypatch.setattr(sys, "argv", [
        "zenolacuna_demo", "--out", str(output), "--tau-bin", str(binary),
    ])

    assert main() == 1

    captured = capsys.readouterr()
    assert json.loads(captured.out) == {
        "status": "REJECTED", "code": "binary_not_executable", "authority": "NONE",
    }
    assert captured.err == ""
    assert not (output / "summary.json").exists()
