"""Subprocess qualification evidence for the finite signal-migration workflow."""

from __future__ import annotations

import json
import os
import stat
import subprocess
import sys
from pathlib import Path
from typing import cast

from tools.zenolacuna_qualify import OWNER_SECRET

_ROOT = Path(__file__).resolve().parents[1]
_RUNNER = _ROOT / "tools" / "zenolacuna_qualify.py"
_PYTHON = _ROOT / ".venv" / "bin" / "python"
if not _PYTHON.is_file():
    _PYTHON = Path(sys.executable)


def _run_runner(output: Path, *extra: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [str(_PYTHON), str(_RUNNER), "--out", str(output), *extra],
        cwd=_ROOT,
        env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
        text=True,
        capture_output=True,
        check=False,
        timeout=600,
    )


def _report(output: Path) -> dict[str, object]:
    report_path = output / "qualification.report.json"
    return cast(dict[str, object], json.loads(report_path.read_text(encoding="ascii")))


def test_public_cli_qualification_completes_and_replays_without_secret_artifacts(tmp_path: Path) -> None:
    output = tmp_path / "qualification"
    result = _run_runner(output)
    assert result.returncode == 0, (result.stdout, result.stderr)
    report = _report(output)

    assert report["status"] == "QUALIFIED"
    assert report["authority"] == "NONE"
    assert report["approval_label"] == "TEST_CREDENTIALS"
    assert report["fixture_kind"] == "TEST_CREDENTIALS_FIXED_OWNER_SECRET"
    assert report["source_execution_context"] == "FRESH_SOURCE_PROCESS"
    assert report["owner_question_count"] == 1
    assert report["declared_fixed_question_baseline"] == 1
    assert report["llm_calls"] == 0

    coverage = cast(dict[str, object], report["coverage"])
    assert coverage == {"code_bug": 1, "missing_requirement": 2, "model_omission": 1}
    hostile = cast(dict[str, object], report["hostile_case_counts"])
    assert hostile["missing_requirement_recoveries"] == 2
    assert hostile["missing_requirement_misses"] == 0
    assert hostile["spurious_witnesses"] == 0
    assert hostile["false_completions"] == 0
    assert "Explicit qualification cases only" in str(hostile["scope"])

    direct = cast(dict[str, object], report["direct_baseline"])
    assert direct["code"] == "SIGNAL_MIGRATION_CHECKED"
    negative = cast(dict[str, object], report["negative_model_omission"])
    assert negative["code"] == "MODEL_OMISSION"
    completion = cast(dict[str, object], report["completion"])
    assert completion["workflow"] == "COMPLETE_FOR_SCOPE"
    certificate = cast(dict[str, object], completion["certificate"])
    assert certificate["checker_sha256"] == report["checker_sha256"]
    assert certificate["sources"]
    runtime = cast(dict[str, object], certificate["runtime"])
    runtime_report = cast(dict[str, object], runtime["report"])
    for field in ("checked_inputs128", "checked_states", "checked_edges"):
        assert runtime_report[field] == direct[field]

    replay = cast(dict[str, object], report["replay"])
    assert replay["scope"] == "EXACT_HISTORICAL_SNAPSHOT"
    assert replay["workflow"] == "COMPLETE_FOR_SCOPE"
    assert replay["certificate_equal"] is True
    assert cast(dict[str, object], report["required_tool_pins"]) == {
        "tau_sha256": None,
        "esso_sha256": None,
    }

    commands = cast(list[dict[str, object]], report["commands"])
    assert commands
    for command in commands:
        argv = cast(list[str], command["argv"])
        assert Path(argv[0]).resolve() == _PYTHON.resolve()
        assert Path(argv[1]).resolve() == (_ROOT / "tools" / "zenolacuna.py").resolve()
        assert "OWNER_SECRET" not in json.dumps(command, sort_keys=True)
        if "--key-file" in argv:
            index = argv.index("--key-file")
            assert argv[index + 1] == "<TEST_OWNER_KEY>"
    assert OWNER_SECRET.hex() not in result.stdout
    assert OWNER_SECRET.hex() not in result.stderr

    for artifact in output.rglob("*"):
        if artifact.is_file():
            data = artifact.read_bytes()
            assert OWNER_SECRET not in data
            assert OWNER_SECRET.hex().encode("ascii") not in data
    assert stat.S_IMODE(output.stat().st_mode) == 0o700
    assert stat.S_IMODE((output / "qualification.report.json").stat().st_mode) == 0o600

    # A qualification directory is immutable evidence; a second run cannot
    # replace its report or silently produce a different receipt.
    repeated = _run_runner(output)
    assert repeated.returncode == 2
    assert json.loads(repeated.stderr)["code"] == "OUTPUT_EXISTS"


def test_failed_cli_tool_never_writes_qualification_summary(tmp_path: Path) -> None:
    output = tmp_path / "failed-qualification"
    result = _run_runner(output, "--tau-bin", str(tmp_path / "missing-tau"))
    assert result.returncode == 2
    assert not (output / "qualification.report.json").exists()
    assert output.is_dir()
    assert "OWNER_SECRET" not in result.stdout + result.stderr
