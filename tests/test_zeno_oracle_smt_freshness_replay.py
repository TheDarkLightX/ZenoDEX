from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.zeno_oracle_smt_freshness_replay import build_status


ROOT = Path(__file__).resolve().parents[1]


def test_smt_freshness_replay_accepts_z3_and_cvc5() -> None:
    status = build_status()

    assert status["schema"] == "zenodex.oracle.smt_freshness_replay.v1"
    assert status["status"] == "accepted"
    assert status["case_count"] == 6
    assert status["failed_count"] == 0
    for case in status["cases"]:
        assert case["ok"] is True
        assert [row["solver"] for row in case["solvers"]] == ["z3", "cvc5"]
        assert [row["status"] for row in case["solvers"]] == ["unsat", "unsat"]


def test_smt_freshness_replay_cli_json() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zeno_oracle_smt_freshness_replay.py", "--format", "json"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    payload = json.loads(proc.stdout)
    assert payload["status"] == "accepted"
