from __future__ import annotations

import re
import subprocess
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin


ROOT = Path(__file__).resolve().parents[2]
NONBYPASS = ROOT / "formal" / "tau" / "proof_obligations" / "settlement_master_nonbypass_v1.tau"
ANSI = re.compile(r"\x1b\[[0-9;]*m")


def _tau_unsat_result(spec_path: Path) -> str:
    tau_bin = find_tau_bin(ROOT, profile="latest")
    if not tau_bin:
        pytest.skip("latest Tau binary not found")
    command = " ".join(
        line
        for line in (raw.strip() for raw in spec_path.read_text(encoding="utf-8").splitlines())
        if line and not line.startswith("#") and line != "set charvar off"
    )
    proc = subprocess.run(
        [tau_bin],
        input=command + "\n",
        capture_output=True,
        text=True,
        timeout=90,
        check=False,
    )
    output = ANSI.sub("", proc.stdout + proc.stderr)
    if "%1: T" in output:
        return "UNSAT"
    if "%1:" in output:
        return "SAT_OR_OTHER"
    return output[:400] or f"NO_OUTPUT rc={proc.returncode}"


def test_settlement_master_nonbypass_unsat_on_latest_tau() -> None:
    assert _tau_unsat_result(NONBYPASS) == "UNSAT"


def test_settlement_master_nonbypass_independent_z3() -> None:
    z3 = pytest.importorskip("z3")
    sreq, cons, fresh, admit = z3.Bools("sreq cons fresh admit")
    a1, a2, a3, a4, target = z3.BitVecs("a1 a2 a3 a4 target", 32)
    delta = a1 + a2 + a3 + a4

    solver = z3.Solver()
    solver.add(
        admit == z3.And(sreq, cons, fresh),
        admit,
        cons == z3.And(z3.ULE(delta, target), z3.UGE(delta, target)),
        delta != target,
    )

    assert solver.check() == z3.unsat


def test_settlement_master_nonbypass_is_not_vacuous() -> None:
    z3 = pytest.importorskip("z3")
    sreq, cons, fresh, admit = z3.Bools("sreq cons fresh admit")
    a1, a2, a3, a4, target = z3.BitVecs("a1 a2 a3 a4 target", 32)
    delta = a1 + a2 + a3 + a4

    solver = z3.Solver()
    solver.add(
        admit == z3.And(sreq, cons, fresh),
        admit,
        cons == z3.And(z3.ULE(delta, target), z3.UGE(delta, target)),
        delta == target,
    )

    assert solver.check() == z3.sat
