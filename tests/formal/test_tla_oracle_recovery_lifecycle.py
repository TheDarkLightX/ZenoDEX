from __future__ import annotations

import json
import shutil
import subprocess
import sys
from pathlib import Path

import pytest


def test_tla_oracle_recovery_public_replay_accepts() -> None:
    root = Path(__file__).resolve().parents[2]
    proc = subprocess.run(
        [
            sys.executable,
            "tools/zeno_oracle_tla_recovery_replay.py",
            "--format",
            "json",
        ],
        cwd=root,
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    receipt = json.loads(proc.stdout)
    assert receipt["schema"] == "zenodex.oracle.tla_recovery_lifecycle_replay.v1"
    assert receipt["status"] == "accepted"
    assert receipt["invariant_violation_count"] == 0
    assert receipt["failed_property_count"] == 0
    property_ids = {prop["id"] for prop in receipt["properties"]}
    assert "FairImpliesEventuallyFreshOrBlocked" in property_ids
    assert "FairImpliesHealthyRequestEventuallyResolved" in property_ids


def test_tla_oracle_recovery_lifecycle_model_checks(tmp_path: Path) -> None:
    from tools.run_tla_models import DEFAULT_JAR, TlaModelError, _find_java, _find_tla_jar

    root = Path(__file__).resolve().parents[2]
    src_cfg = root / "formal" / "tla" / "OracleRecoveryLifecycle.cfg"
    src_tla = root / "formal" / "tla" / "OracleRecoveryLifecycle.tla"
    model_dir = tmp_path / "tla"
    model_dir.mkdir(parents=True, exist_ok=True)
    cfg = model_dir / "OracleRecoveryLifecycle.cfg"
    tla = model_dir / "OracleRecoveryLifecycle.tla"
    shutil.copyfile(src_cfg, cfg)
    shutil.copyfile(src_tla, tla)
    log_dir = tmp_path / "logs"
    log_dir.mkdir(parents=True, exist_ok=True)
    log_path = log_dir / "OracleRecoveryLifecycle.log"

    try:
        java = _find_java(None)
        jar = _find_tla_jar(DEFAULT_JAR)
    except TlaModelError as exc:  # pragma: no cover - toolchain-dependent
        pytest.skip(str(exc))

    cmd = [
        java,
        "-XX:+UseParallelGC",
        "-cp",
        str(jar),
        "tlc2.TLC",
        "-cleanup",
        "-config",
        str(cfg),
        str(tla),
    ]
    with log_path.open("w", encoding="utf-8") as fh:
        proc = subprocess.run(
            cmd,
            cwd=model_dir,
            stdout=fh,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=60,
            check=False,
        )

    assert proc.returncode == 0, log_path.read_text(encoding="utf-8")
    log_text = log_path.read_text(encoding="utf-8")
    assert "OracleRecoveryLifecycle" in log_text
    assert "No error has been found." in log_text
