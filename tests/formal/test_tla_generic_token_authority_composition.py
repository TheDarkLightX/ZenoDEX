from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest


def _tla_toolchain() -> tuple[str, Path]:
    from tools.run_tla_models import (
        DEFAULT_JAR,
        TlaModelError,
        _find_java,
        _find_tla_jar,
    )

    try:
        return _find_java(None), _find_tla_jar(DEFAULT_JAR)
    except TlaModelError as exc:  # pragma: no cover - toolchain-dependent
        pytest.skip(str(exc))


def _run_tlc(model_dir: Path, model_name: str) -> tuple[int, str]:
    java, jar = _tla_toolchain()
    cfg = model_dir / f"{model_name}.cfg"
    tla = model_dir / f"{model_name}.tla"
    log_path = model_dir / f"{model_name}.log"
    command = [
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
    with log_path.open("w", encoding="utf-8") as handle:
        process = subprocess.run(
            command,
            cwd=model_dir,
            stdout=handle,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=60,
            check=False,
        )
    return process.returncode, log_path.read_text(encoding="utf-8")


def _copy_model(tmp_path: Path) -> tuple[Path, str]:
    root = Path(__file__).resolve().parents[2]
    model_name = "GenericTokenAuthorityComposition"
    source_dir = root / "formal" / "tla"
    model_dir = tmp_path / "tla"
    model_dir.mkdir(parents=True, exist_ok=True)
    cfg = model_dir / f"{model_name}.cfg"
    tla = model_dir / f"{model_name}.tla"
    shutil.copyfile(source_dir / cfg.name, cfg)
    shutil.copyfile(source_dir / tla.name, tla)
    return model_dir, model_name


def test_tla_generic_token_authority_composition_model_checks(
    tmp_path: Path,
) -> None:
    model_dir, model_name = _copy_model(tmp_path)
    returncode, log_text = _run_tlc(model_dir, model_name)
    assert returncode == 0, log_text
    assert model_name in log_text
    assert "No error has been found." in log_text


def test_tla_model_detects_missing_accounting_commit_guard(
    tmp_path: Path,
) -> None:
    model_dir, model_name = _copy_model(tmp_path)
    tla = model_dir / f"{model_name}.tla"
    source = tla.read_text(encoding="utf-8")
    guard = "  /\\ AccountingOK(staged)\n"
    assert source.count(guard) == 1
    tla.write_text(source.replace(guard, "", 1), encoding="utf-8")

    returncode, log_text = _run_tlc(model_dir, model_name)
    assert returncode != 0
    assert "Invariant CommittedAccountingOK is violated" in log_text
