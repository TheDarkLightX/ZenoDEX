from __future__ import annotations

import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

TARGET = "Proofs.RouteProtocolFeeConservation"
MAX_LEAN_CPUS = 4


def _bounded_lake_command(lake: str) -> list[str]:
    """Return a fail-closed, CPU-bounded Lake invocation for Linux CI."""
    if not sys.platform.startswith("linux"):
        pytest.skip("bounded Lean build requires Linux CPU affinity support")

    taskset = shutil.which("taskset")
    nice = shutil.which("nice")
    if taskset is None or nice is None or not hasattr(os, "sched_getaffinity"):
        pytest.skip("bounded Lean build requires taskset, nice, and CPU affinity")

    affinity = sorted(os.sched_getaffinity(0))
    if not affinity:
        pytest.skip("bounded Lean build has no available CPUs")
    cpu_list = ",".join(str(cpu) for cpu in affinity[:MAX_LEAN_CPUS])
    return [
        taskset,
        "-c",
        cpu_list,
        nice,
        "-n",
        "10",
        lake,
        "--wfail",
        "build",
        TARGET,
    ]


def test_lean_route_protocol_fee_conservation_builds_without_warnings() -> None:
    lake = shutil.which("lake")
    if not lake:
        pytest.skip("lake not installed")

    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    if not (root / "external" / "mathlib4").exists():
        pytest.skip("mathlib4 checkout missing")

    try:
        proc = subprocess.run(
            _bounded_lake_command(lake),
            cwd=lean_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=240,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        pytest.fail(
            f"lake --wfail build timed out after {exc.timeout}s for {TARGET}"
        )

    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_lean_route_protocol_fee_conservation_is_exported() -> None:
    root = Path(__file__).resolve().parents[2]
    exports = (root / "lean-mathlib" / "Proofs.lean").read_text(encoding="utf-8")
    assert "import Proofs.RouteProtocolFeeConservation" in exports
