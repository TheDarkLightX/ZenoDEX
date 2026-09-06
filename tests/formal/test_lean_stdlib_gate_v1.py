"""Fail-closed controls for the isolated standard-library Lean gate.

The consumer mutation uses one unchanged small proof and the installed pinned
Lean executable. The subprocess failure cases are deliberately mocked: they
exercise only shell-error handling and do not claim compiler execution.
"""

from __future__ import annotations

import subprocess
from pathlib import Path

import pytest

from tests.formal.lean_stdlib_gate_v1 import (
    TheoremReference,
    _check_axioms,
    _run,
    check_lean_stdlib_source,
)


def test_wrong_independent_consumer_type_fails_pinned_lean(tmp_path: Path) -> None:
    """A typed consumer mismatch must fail the real pinned compiler."""

    reference = TheoremReference(
        "TauSwap.AutoTrader.BinaryDecision.winnerPair_ge_noop",
        "∀ (emitRequested emitAdmissible : Bool), Bool",
    )
    with pytest.raises(pytest.fail.Exception, match="(?i)type mismatch"):
        check_lean_stdlib_source(
            "Proofs/ZenoDEXAutoTraderBinaryDecision.lean",
            (reference,),
            tmp_path,
        )


@pytest.mark.parametrize(
    ("case", "output", "message"),
    (
        ("missing", "", "missing unique"),
        (
            "duplicate",
            "'Demo.claim' depends on axioms: [propext]\n"
            "'Demo.claim' depends on axioms: [propext]",
            "missing unique",
        ),
        (
            "nonstandard",
            "'Demo.claim' depends on axioms: [Demo.trustMe]",
            "non-standard axioms",
        ),
    ),
)
def test_axiom_report_anomalies_fail_closed(
    case: str,
    output: str,
    message: str,
) -> None:
    """Missing, duplicate, and unapproved axiom reports must be rejected."""

    del case
    reference = TheoremReference("Demo.claim", "Nat")
    with pytest.raises(pytest.fail.Exception, match=message):
        _check_axioms(output, (reference,))


@pytest.mark.parametrize("failure", ("nonzero", "timeout"))
def test_compiler_shell_failures_fail_closed(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    failure: str,
) -> None:
    """Mocked subprocess failures cover shell handling only, never Lean claims."""

    def fake_run(*args: object, **kwargs: object) -> subprocess.CompletedProcess[str]:
        del args, kwargs
        if failure == "timeout":
            raise subprocess.TimeoutExpired(cmd="lean", timeout=120)
        return subprocess.CompletedProcess(
            args=["lean"], returncode=1, stdout="", stderr="compiler failed"
        )

    monkeypatch.setattr(subprocess, "run", fake_run)
    with pytest.raises(pytest.fail.Exception):
        _run(Path("lean"), [], cwd=tmp_path)
