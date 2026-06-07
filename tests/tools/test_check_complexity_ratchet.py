from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

TOOL = Path("tools/check_complexity_ratchet.py")


def _run_tool(*args: str | Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(TOOL), *(str(arg) for arg in args)],
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


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

    write_result = _run_tool(module, "--baseline", baseline, "--write-baseline")
    assert write_result.returncode == 0, write_result.stderr

    check_result = _run_tool(module, "--baseline", baseline, "--json")
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

    result = _run_tool(module, "--strict", "--json")
    assert result.returncode == 1
    payload = json.loads(result.stdout)
    assert payload["ok"] is False
    assert payload["over_complexity_budget_count"] == 1


def test_complexity_ratchet_rejects_existing_function_complexity_regression(
    tmp_path: Path,
) -> None:
    """Default mode rejects per-function growth that aggregate counters miss."""
    huge = _write_module(
        tmp_path / "huge.py",
        "def huge(a, b, c, d, e, f, g, h, i, j):\n"
        "    if a: pass\n"
        "    if b: pass\n"
        "    if c: pass\n"
        "    if d: pass\n"
        "    if e: pass\n"
        "    if f: pass\n"
        "    if g: pass\n"
        "    if h: pass\n"
        "    if i: pass\n"
        "    if j: pass\n"
        "    return 0\n",
    )
    target = _write_module(
        tmp_path / "target.py",
        "def target(a, b, c, d, e):\n"
        "    if a: pass\n"
        "    if b: pass\n"
        "    if c: pass\n"
        "    if d: pass\n"
        "    if e: pass\n"
        "    return 0\n",
    )
    baseline = tmp_path / "baseline.json"
    assert _run_tool(huge, target, "--baseline", baseline, "--write-baseline").returncode == 0

    _write_module(
        target,
        "def target(a, b, c, d, e, f, g, h, i):\n"
        "    if a: pass\n"
        "    if b: pass\n"
        "    if c: pass\n"
        "    if d: pass\n"
        "    if e: pass\n"
        "    if f: pass\n"
        "    if g: pass\n"
        "    if h: pass\n"
        "    if i: pass\n"
        "    return 0\n",
    )

    result = _run_tool(huge, target, "--baseline", baseline, "--json")
    payload = json.loads(result.stdout)
    assert result.returncode == 1
    assert payload["ok"] is False
    assert any("target.py::target complexity worsened" in error for error in payload["errors"])


def test_complexity_ratchet_rejects_new_over_budget_function_even_when_hotspot_removed(
    tmp_path: Path,
) -> None:
    """Deleting one hotspot cannot hide a newly introduced over-budget function."""
    old_hotspot = _write_module(
        tmp_path / "old_hotspot.py",
        "def old_hotspot(a, b, c, d, e, f):\n"
        "    if a: pass\n"
        "    if b: pass\n"
        "    if c: pass\n"
        "    if d: pass\n"
        "    if e: pass\n"
        "    if f: pass\n"
        "    return 0\n",
    )
    baseline = tmp_path / "baseline.json"
    assert _run_tool(tmp_path, "--baseline", baseline, "--write-baseline").returncode == 0

    old_hotspot.unlink()
    _write_module(
        tmp_path / "new_hotspot.py",
        "def new_hotspot(a, b, c, d, e, f):\n"
        "    if a: pass\n"
        "    if b: pass\n"
        "    if c: pass\n"
        "    if d: pass\n"
        "    if e: pass\n"
        "    if f: pass\n"
        "    return 0\n",
    )

    result = _run_tool(tmp_path, "--baseline", baseline, "--json")
    payload = json.loads(result.stdout)
    assert result.returncode == 1
    assert any("new function exceeds complexity budget" in error for error in payload["errors"])


def test_complexity_ratchet_rejects_existing_function_length_regression(tmp_path: Path) -> None:
    """Default mode catches line growth below the global max-function length."""
    long_function_body = "\n".join("    x = 1" for _ in range(80))
    long_function = _write_module(
        tmp_path / "long.py",
        f"def long_function():\n{long_function_body}\n    return 1\n",
    )
    target = _write_module(
        tmp_path / "target.py",
        "def target():\n"
        "    x = 1\n"
        "    return x\n",
    )
    baseline = tmp_path / "baseline.json"
    assert _run_tool(long_function, target, "--baseline", baseline, "--write-baseline").returncode == 0

    _write_module(
        target,
        "def target():\n"
        "    x = 1\n"
        "    x = 2\n"
        "    x = 3\n"
        "    x = 4\n"
        "    return x\n",
    )

    result = _run_tool(long_function, target, "--baseline", baseline, "--json")
    payload = json.loads(result.stdout)
    assert result.returncode == 1
    assert any("target.py::target length worsened" in error for error in payload["errors"])


def test_complexity_ratchet_strict_mode_counts_match_cases(tmp_path: Path) -> None:
    """Python match statements count as branch complexity."""
    module = _write_module(
        tmp_path / "matcher.py",
        "def matcher(value):\n"
        "    match value:\n"
        "        case 0:\n"
        "            return 0\n"
        "        case 1:\n"
        "            return 1\n"
        "        case 2:\n"
        "            return 2\n"
        "        case 3:\n"
        "            return 3\n"
        "        case 4:\n"
        "            return 4\n"
        "        case _:\n"
        "            return 5\n",
    )

    result = _run_tool(module, "--strict", "--json")
    payload = json.loads(result.stdout)
    assert result.returncode == 1
    assert payload["over_complexity_budget_count"] == 1


def test_complexity_ratchet_does_not_charge_nested_function_body_to_outer(
    tmp_path: Path,
) -> None:
    """Nested helpers are measured independently, not charged to the parent."""
    module = _write_module(
        tmp_path / "nested.py",
        "def outer():\n"
        "    def nested(a, b, c, d, e, f):\n"
        "        if a: pass\n"
        "        if b: pass\n"
        "        if c: pass\n"
        "        if d: pass\n"
        "        if e: pass\n"
        "        if f: pass\n"
        "        return 1\n"
        "    return nested\n",
    )

    result = _run_tool(module, "--strict", "--json")
    payload = json.loads(result.stdout)
    assert result.returncode == 1
    assert payload["functions"][f"{module.as_posix()}::outer"]["complexity"] == 1
    assert payload["functions"][f"{module.as_posix()}::outer.nested"]["complexity"] > 5
