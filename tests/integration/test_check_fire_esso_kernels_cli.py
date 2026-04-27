from __future__ import annotations

import json
import importlib.util
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[2]
CHECK_CLI = REPO_ROOT / "tools" / "check_fire_esso_kernels.py"


def _esso_available() -> bool:
    return importlib.util.find_spec("ESSO") is not None


@pytest.mark.skipif(
    os.environ.get("ZENO_SKIP_ESSO") == "1" or not _esso_available(),
    reason="ESSO checks disabled or ESSO module unavailable",
)
def test_check_fire_esso_kernels_cli_roundtrip() -> None:
    output_dir = REPO_ROOT / "internal" / "test_artifacts" / "fire_esso_cli"
    if output_dir.exists():
        shutil.rmtree(output_dir)
    proc = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            "--output-dir",
            str(output_dir),
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["schema"] == "zenodex/fire-esso-kernel-check-report/v1"
    assert report["ok"] is True
    assert report["case_count"] == 3
    assert report["solvers"] == ["z3", "cvc5"]
    assert report["python_executable"] == sys.executable
    assert "ESSO" in report["esso_module_path"]
    assert "z3" in report["solver_versions"]
    assert "cvc5" in report["solver_versions"]
    assert Path(report["report_path"]).is_file()
    for case in report["cases"]:
        assert case["ok"] is True
        assert case["validate_ok"] is True
        assert case["verify_ok"] is True
        assert case["determinism"] is True
        assert case["verdict"] == "VERIFIED"
        assert case["inconclusive_queries"] == 0
        assert case["solvers_agreed"] is True
        assert Path(case["validate_artifact_path"]).is_file()
        assert Path(case["verify_artifact_path"]).is_file()
