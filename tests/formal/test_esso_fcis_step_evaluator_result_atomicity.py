from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
SAFE_MODEL = ROOT / "formal" / "esso" / "fcis_step_evaluator_result_atomicity_v1.yaml"
UNSAFE_MODEL = ROOT / "formal" / "esso" / "fcis_step_evaluator_result_atomicity_unsafe_v1.yaml"


pytestmark = pytest.mark.skipif(
    importlib.util.find_spec("ESSO") is None,
    reason="ESSO is not available",
)


def _run_esso(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, "-m", "ESSO", *args],
        check=False,
        capture_output=True,
        text=True,
    )


def _payload(result: subprocess.CompletedProcess[str]) -> dict[str, object]:
    assert result.stdout
    payload = json.loads(result.stdout)
    assert type(payload) is dict
    return payload


@pytest.mark.parametrize("model", (SAFE_MODEL, UNSAFE_MODEL))
def test_fcis_step_evaluator_result_model_validates(model: Path) -> None:
    result = _run_esso("validate", str(model))

    assert result.returncode == 0, result.stderr
    assert _payload(result)["ok"] is True


def test_fcis_step_evaluator_result_atomicity_is_inductive(tmp_path: Path) -> None:
    result = _run_esso(
        "verify",
        str(SAFE_MODEL),
        "--reference",
        str(SAFE_MODEL),
        "--output",
        str(tmp_path / "safe"),
    )

    assert result.returncode == 0, result.stderr
    payload = _payload(result)
    assert payload["ok"] is True
    invariant = payload["invariant_inductive"]
    assert type(invariant) is dict
    assert invariant["status"] == "PASS"


def test_fcis_step_evaluator_candidate_leak_control_is_rejected(
    tmp_path: Path,
) -> None:
    result = _run_esso(
        "verify",
        str(UNSAFE_MODEL),
        "--reference",
        str(UNSAFE_MODEL),
        "--output",
        str(tmp_path / "unsafe"),
    )

    assert result.returncode != 0
    payload = _payload(result)
    assert payload["ok"] is False
    invariant = payload["invariant_inductive"]
    assert type(invariant) is dict
    counterexample = invariant["counterexample"]
    assert type(counterexample) is dict
    command = counterexample["command"]
    assert type(command) is dict
    assert command["tag"] == "reject_with_candidate_leak"
