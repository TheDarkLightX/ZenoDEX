"""Benign local process fixtures for the research runner's resource boundary."""

import fcntl
import hashlib
import json
import os
import sys
from pathlib import Path

import pytest

from experiments.tau_adt_rows_v1 import execution, qualify


def _python(code: str) -> tuple[str, ...]:
    return (sys.executable, "-I", "-S", "-c", code)


def test_executable_snapshot_is_sealed_and_survives_source_replacement(tmp_path: Path) -> None:
    # This is a copy/sealing fixture, never an executable process fixture.
    payload = b"\x7fELFbounded-copy-fixture"
    source = tmp_path / "source"
    source.write_bytes(payload)
    with execution.frozen_executable(source, hashlib.sha256(payload).hexdigest()) as descriptor:
        source.write_bytes(b"replaced source bytes")
        assert os.read(descriptor, 65536) == payload
        seals = fcntl.fcntl(descriptor, fcntl.F_GET_SEALS)
        required = fcntl.F_SEAL_SEAL | fcntl.F_SEAL_WRITE | fcntl.F_SEAL_GROW | fcntl.F_SEAL_SHRINK
        assert seals & required == required
        with pytest.raises(OSError):
            os.write(descriptor, b"change")


def test_process_preserves_raw_lf_and_bounds_exact_stdout_limit() -> None:
    echoed = execution.run_bounded(_python("import sys; sys.stdout.buffer.write(sys.stdin.buffer.read())"), b"hello\n")
    assert (echoed.returncode, echoed.stdout, echoed.stderr) == (0, "hello\n", "")
    boundary = execution.run_bounded(_python("import os; os.write(1, b'x'*65536)"), b"")
    assert len(boundary.stdout) == 65536


@pytest.mark.parametrize(("descriptor", "length", "label"), ((1, 65537, "stdout"), (2, 4097, "stderr")))
def test_process_rejects_output_ceiling_before_decoder(descriptor: int, length: int, label: str) -> None:
    with pytest.raises(ValueError, match=label + " limit exceeded"):
        execution.run_bounded(_python(f"import os; os.write({descriptor}, b'x'*{length})"), b"")


@pytest.mark.parametrize("payload", (b"row\r", b"row\r\n", b"\xff"))
def test_process_rejects_noncanonical_raw_transcripts(payload: bytes) -> None:
    with pytest.raises(ValueError):
        execution.run_bounded(_python(f"import os; os.write(1, {payload!r})"), b"")


def test_process_deadline_uses_one_absolute_budget(monkeypatch: pytest.MonkeyPatch) -> None:
    ticks = iter((0, 1_000_000))
    monkeypatch.setattr(execution, "monotonic_ns", lambda: next(ticks))
    with pytest.raises(ValueError, match="deadline exceeded"):
        execution.run_bounded(_python("pass"), b"", timeout_ms=1)


def test_cli_report_write_failure_is_json_fail(tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]) -> None:
    monkeypatch.setattr(qualify, "run_qualification", lambda binary: {"status": "PASS"})
    monkeypatch.setattr(sys, "argv", ["qualify", "--tau-binary", "unused", "--output", str(tmp_path)])
    assert qualify.main() == 1
    assert json.loads(capsys.readouterr().out)["status"] == "FAIL"


def test_failed_qualification_replaces_a_previous_pass_report(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    report = tmp_path / "report.json"
    report.write_text('{"status":"PASS"}')
    missing = tmp_path / "missing-tau"
    monkeypatch.setattr(sys, "argv", ["qualify", "--tau-binary", str(missing), "--output", str(report)])
    assert qualify.main() == 1
    assert json.loads(report.read_text())["status"] == "FAIL"
