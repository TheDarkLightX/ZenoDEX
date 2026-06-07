from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

TOOL = Path("tools/check_complexity_ratchet.py")


def _write_module(path: Path, source: str) -> Path:
    path.write_text(source, encoding="utf-8")
    return path


def test_complexity_ratchet_accepts_non_worsening_baseline(tmp_path: Path) -> None:
    """Baseline mode permits legacy debt only when metrics do not worsen."""
    module = _write_module(
        tmp_path / "sample.py",
        "def f(x):\n"
        "    if x:\n"
        "        return 1\n"
        "    return 0\n",
    )
    baseline = tmp_path / "baseline.json"

    write_result = subprocess.run(
        [sys.executable, str(TOOL), str(module), "--baseline", str(baseline), "--write-baseline"],
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    assert write_result.returncode == 0, write_result.stderr

    check_result = subprocess.run(
        [sys.executable, str(TOOL), str(module), "--baseline", str(baseline), "--json"],
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    assert check_result.returncode == 0, check_result.stderr
    assert json.loads(check_result.stdout)["ok"] is True


def test_complexity_ratchet_strict_mode_rejects_branchy_function(tmp_path: Path) -> None:
    """Strict mode enforces the A-grade target for new/touched code."""
    module = _write_module(
        tmp_path / "branchy.py",
        "def branchy(a, b, c, d, e, f):\n"
        "    if a:\n"
        "        pass\n"
        "    if b:\n"
        "        pass\n"
        "    if c:\n"
        "        pass\n"
        "    if d:\n"
        "        pass\n"
        "    if e:\n"
        "        pass\n"
        "    if f:\n"
        "        pass\n"
        "    return 0\n",
    )

    result = subprocess.run(
        [sys.executable, str(TOOL), str(module), "--strict", "--json"],
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    assert result.returncode == 1
    payload = json.loads(result.stdout)
    assert payload["ok"] is False
    assert payload["over_complexity_budget_count"] == 1
