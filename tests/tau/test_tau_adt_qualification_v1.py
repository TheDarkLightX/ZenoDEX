"""Offline negative controls for the explicit Tau execution probe."""

from pathlib import Path
from subprocess import CompletedProcess

import pytest

from experiments.tau_adt_rows_v1.qualify import (
    _reference_identity,
    _require_malformed_rejection,
    _scalar_values,
    run_qualification,
)
from experiments.tau_adt_rows_v1.row_codec import INPUT_BANNER_V1, OUTPUT_BANNER_V1, TYPE_BANNER_V1


def _transcript(rows: str, width: int = 128) -> str:
    return f"[1] i:bv[{width}] := in /dev/stdin.\n[2] o:bv[{width}] := out console.\n" + rows


def test_scalar_reference_retains_integer_boundaries_and_identity_positions() -> None:
    assert _scalar_values(_transcript(f"o[0] := 0\n\tstep: 1.25 ms\no[1] := {2**128 - 1}\n"), "", 128, 2) == (0, 2**128 - 1)
    assert _scalar_values(_transcript("", 1280), "", 1280, 0) == ()
    assert _reference_identity("A") == 65 * 2**1272
    assert _reference_identity("AB") == 65 * 2**1272 + 66 * 2**1264
    assert _reference_identity("!" * 160) == 33 * (2**1280 - 1) // 255


@pytest.mark.parametrize("rows", (
    "", "o[0] := 1\nError: trailing diagnostic\n", "o[00] := 1\n",
    "o[1] := 1\n", "o[0] := 01\n", "o[0] := -1\n",
    "o[0] := 1\no[0] := 1\n", f"o[0] := {2**128}\n",
    "\tstep: 1 ms\no[0] := 1\n", "o[0] := predicate(?)\n",
    "o[0] := " + "1" * 65536,
))
def test_scalar_decoder_rejects_incomplete_noncanonical_or_extra_output(rows: str) -> None:
    with pytest.raises(ValueError):
        _scalar_values(_transcript(rows), "", 128, 1)


def test_scalar_decoder_rejects_stderr_wrong_schema_and_foreign_binary(tmp_path: Path) -> None:
    with pytest.raises(ValueError):
        _scalar_values(_transcript("o[0] := 1\n"), "error", 128, 1)
    with pytest.raises(ValueError):
        _scalar_values(_transcript("o[0] := 1\n", 1280), "", 128, 1)
    foreign = tmp_path / "foreign-tau"
    foreign.write_bytes(b"This file must never be executed")
    with pytest.raises(ValueError, match="differs from the measured"):
        run_qualification(foreign)


@pytest.mark.parametrize(("code", "stdout", "stderr"), (
    (-11, "Error", ""), (1, "Error", ""), (2, "", "startup failed"),
    (0, "", ""), (0, "Error", "unexpected stderr"), (0, "NotAnErrorDiagnostic", ""),
))
def test_crash_or_missing_diagnostic_cannot_count_as_negative_qualification(code: int, stdout: str, stderr: str) -> None:
    with pytest.raises(ValueError, match="normal pinned-engine error diagnostic"):
        _require_malformed_rejection(CompletedProcess((), code, stdout, stderr), "missing_field")


def test_clean_engine_diagnostic_must_also_reject_through_adapter() -> None:
    transcript = "\n".join((TYPE_BANNER_V1, INPUT_BANNER_V1, OUTPUT_BANNER_V1,
        "(\x1b[31;1mError\x1b[0m) ADT wire: missing key 'amount_atoms' at ''",
        "(\x1b[31;1mError\x1b[0m) Failed to read from input stream 'i.amount_atoms'", ""))
    _require_malformed_rejection(CompletedProcess((), 0, transcript, ""), "missing_field")
    with pytest.raises(ValueError):
        _require_malformed_rejection(CompletedProcess((), 0, transcript.replace("missing key", "unrelated failure"), ""), "missing_field")
