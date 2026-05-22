from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest


def test_tla_settlement_witness_bounded_open_ingress_model_checks(tmp_path: Path) -> None:
    from tools.run_tla_models import DEFAULT_JAR, TlaModelError, _find_java, _find_tla_jar

    root = Path(__file__).resolve().parents[2]
    src_cfg = root / "formal" / "tla" / "SettlementWitnessBoundedOpenIngress.cfg"
    src_tla = root / "formal" / "tla" / "SettlementWitnessBoundedOpenIngress.tla"
    model_dir = tmp_path / "tla"
    model_dir.mkdir(parents=True, exist_ok=True)
    cfg = model_dir / "SettlementWitnessBoundedOpenIngress.cfg"
    tla = model_dir / "SettlementWitnessBoundedOpenIngress.tla"
    shutil.copyfile(src_cfg, cfg)
    shutil.copyfile(src_tla, tla)
    log_dir = tmp_path / "logs"
    log_dir.mkdir(parents=True, exist_ok=True)
    log_path = log_dir / "SettlementWitnessBoundedOpenIngress.log"

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
    content = log_path.read_text(encoding="utf-8")
    assert "SettlementWitnessBoundedOpenIngress" in content
    assert "No error has been found." in content
