from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path

import pytest
import yaml

ROOT = Path(__file__).resolve().parents[2]
MODEL = ROOT / "src" / "kernels" / "dex" / "zusd_protocol_fee_accrual_allocation_v1.yaml"
ESSO_ROOT = Path(os.environ["ESSO_ROOT"]) if os.environ.get("ESSO_ROOT") else None
ESSO_AVAILABLE = importlib.util.find_spec("ESSO") is not None or (
    ESSO_ROOT is not None and (ESSO_ROOT / "ESSO").is_dir()
)


def _esso_env() -> dict[str, str]:
    env = os.environ.copy()
    if ESSO_ROOT is not None:
        prior_pythonpath = env.get("PYTHONPATH")
        env["PYTHONPATH"] = str(ESSO_ROOT) + (
            os.pathsep + prior_pythonpath if prior_pythonpath else ""
        )
    return env


def _verify(model: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            sys.executable,
            "-m",
            "ESSO",
            "verify-multi",
            str(model),
            "--solvers",
            "z3,cvc5",
            "--determinism-trials",
            "2",
            "--timeout-ms",
            "5000",
        ],
        cwd=str(ROOT),
        capture_output=True,
        text=True,
        check=False,
        timeout=90,
        env=_esso_env(),
    )


@pytest.mark.skipif(not ESSO_AVAILABLE, reason="ESSO is not available")
def test_esso_zusd_protocol_fee_accrual_allocation_v1_verifies() -> None:
    validate = subprocess.run(
        [sys.executable, "-m", "ESSO", "validate", str(MODEL)],
        cwd=str(ROOT),
        capture_output=True,
        text=True,
        check=False,
        timeout=90,
        env=_esso_env(),
    )
    assert validate.returncode == 0, validate.stderr or validate.stdout

    verify = _verify(MODEL)
    assert verify.returncode == 0, verify.stderr or verify.stdout
    report = json.loads(verify.stdout)
    assert report["ok"] is True
    assert report["determinism"] is True
    assert report["report"]["verdict"] == "VERIFIED"
    assert report["report"]["solvers_agreed"] is True
    assert report["report"]["failed_queries"] == 0


@pytest.mark.skipif(not ESSO_AVAILABLE, reason="ESSO is not available")
@pytest.mark.parametrize(
    ("guard_index", "mutant_name"),
    (
        (0, "configuration_guard_removed"),
        (1, "scalar_custody_guard_removed"),
        (2, "apportionment_lineage_guard_removed"),
        (3, "allocation_conservation_guard_removed"),
    ),
)
def test_esso_zusd_protocol_fee_accrual_allocation_v1_kills_guard_mutants(
    tmp_path: Path,
    guard_index: int,
    mutant_name: str,
) -> None:
    document = yaml.safe_load(MODEL.read_text(encoding="utf-8"))
    document["actions"][0]["guard"]["args"][guard_index] = {"bool": True}
    mutant = tmp_path / f"{mutant_name}.yaml"
    mutant.write_text(yaml.safe_dump(document, sort_keys=False), encoding="utf-8")

    verify = _verify(mutant)
    assert verify.returncode != 0, f"semantic mutant survived: {mutant_name}"
    report = json.loads(verify.stdout)
    assert report["ok"] is False
    assert report["report"]["failed_queries"] > 0


@pytest.mark.skipif(not ESSO_AVAILABLE, reason="ESSO is not available")
@pytest.mark.parametrize(
    ("update_index", "state_var", "mutant_name"),
    (
        (1, "scalar_cumulative", "scalar_cumulative_accrual_removed"),
        (5, "buyback_cumulative", "buyback_cumulative_accrual_removed"),
        (6, "treasury_cumulative", "treasury_cumulative_accrual_removed"),
        (7, "rewards_cumulative", "rewards_cumulative_accrual_removed"),
    ),
)
def test_esso_zusd_protocol_fee_accrual_allocation_v1_kills_update_mutants(
    tmp_path: Path,
    update_index: int,
    state_var: str,
    mutant_name: str,
) -> None:
    document = yaml.safe_load(MODEL.read_text(encoding="utf-8"))
    document["actions"][0]["updates"][update_index]["expr"] = {"var": state_var}
    mutant = tmp_path / f"{mutant_name}.yaml"
    mutant.write_text(yaml.safe_dump(document, sort_keys=False), encoding="utf-8")

    verify = _verify(mutant)
    assert verify.returncode != 0, f"semantic mutant survived: {mutant_name}"
    report = json.loads(verify.stdout)
    assert report["ok"] is False
    assert report["report"]["failed_queries"] > 0
