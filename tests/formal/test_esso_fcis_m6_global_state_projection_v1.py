"""Dual-solver, registry-parity, and guard-mutant tests for content projection."""

from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path

import pytest
import yaml

from src.core.fcis_m6_global_state_projection_v1 import (
    M6_KNOWN_GLOBAL_PROJECTION_GAPS_V1,
    M6_PROJECTION_AUTHORITY_OBLIGATIONS_V1,
    M6_REQUIRED_APPLICATION_STATE_COMPONENTS_V1,
)

ROOT = Path(__file__).resolve().parents[2]
CONTENT_MODEL = ROOT / "src" / "kernels" / "dex" / "fcis_m6_tau_zenoledger_projection_v1.yaml"
QUALIFICATION_MODEL = (
    ROOT / "src" / "kernels" / "dex" / "fcis_m6_global_state_qualification_v1.yaml"
)
ESSO_ROOT = Path(os.environ["ESSO_ROOT"]) if os.environ.get("ESSO_ROOT") else None
ESSO_AVAILABLE = importlib.util.find_spec("ESSO") is not None or (
    ESSO_ROOT is not None and (ESSO_ROOT / "ESSO").is_dir()
)


def _esso_env() -> dict[str, str]:
    env = os.environ.copy()
    if ESSO_ROOT is not None:
        prior = env.get("PYTHONPATH")
        env["PYTHONPATH"] = str(ESSO_ROOT) + (os.pathsep + prior if prior else "")
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


def test_formal_metadata_matches_every_runtime_closed_registry() -> None:
    content = yaml.safe_load(CONTENT_MODEL.read_text(encoding="utf-8"))
    qualification = yaml.safe_load(QUALIFICATION_MODEL.read_text(encoding="utf-8"))
    assert content["meta"]["component_registry"] == [
        component.value for component in M6_REQUIRED_APPLICATION_STATE_COMPONENTS_V1
    ]
    assert qualification["meta"]["global_gap_registry"] == [
        gap.value for gap in M6_KNOWN_GLOBAL_PROJECTION_GAPS_V1
    ]
    assert qualification["meta"]["authority_obligation_registry"] == [
        obligation.value for obligation in M6_PROJECTION_AUTHORITY_OBLIGATIONS_V1
    ]


def test_registry_omission_mutant_is_killed_by_runtime_model_parity() -> None:
    content = yaml.safe_load(CONTENT_MODEL.read_text(encoding="utf-8"))
    content["meta"]["component_registry"].pop()
    assert content["meta"]["component_registry"] != [
        component.value for component in M6_REQUIRED_APPLICATION_STATE_COMPONENTS_V1
    ]


@pytest.mark.skipif(not ESSO_AVAILABLE, reason="ESSO is not available")
@pytest.mark.parametrize("model", (CONTENT_MODEL, QUALIFICATION_MODEL))
def test_projection_models_validate_and_dual_solvers_agree(model: Path) -> None:
    validate = subprocess.run(
        [sys.executable, "-m", "ESSO", "validate", str(model)],
        cwd=str(ROOT),
        capture_output=True,
        text=True,
        check=False,
        timeout=90,
        env=_esso_env(),
    )
    assert validate.returncode == 0, validate.stderr or validate.stdout
    verify = _verify(model)
    assert verify.returncode == 0, verify.stderr or verify.stdout
    report = json.loads(verify.stdout)
    assert report["ok"] is True
    assert report["determinism"] is True
    assert report["report"]["verdict"] == "VERIFIED"
    assert report["report"]["solvers_agreed"] is True


@pytest.mark.skipif(not ESSO_AVAILABLE, reason="ESSO is not available")
@pytest.mark.parametrize(
    ("action_index", "guard_index", "mutant_name"),
    (
        (0, 0, "tau_canonical_guard_removed"),
        (0, 1, "tau_commitment_guard_removed"),
        (0, 2, "tau_component_derivation_guard_removed"),
        (0, 3, "tau_coverage_guard_removed"),
        (0, 4, "tau_registry_guard_removed"),
        (1, 0, "ledger_header_body_guard_removed"),
        (1, 1, "ledger_post_state_guard_removed"),
        (1, 2, "ledger_component_derivation_guard_removed"),
        (1, 3, "ledger_coverage_guard_removed"),
        (1, 4, "ledger_registry_guard_removed"),
        (2, 0, "parity_tau_admission_guard_removed"),
        (2, 1, "parity_ledger_admission_guard_removed"),
        (2, 2, "parity_source_kind_guard_removed"),
        (2, 3, "parity_content_equality_guard_removed"),
    ),
)
def test_content_model_kills_every_admission_guard_mutant(
    tmp_path: Path,
    action_index: int,
    guard_index: int,
    mutant_name: str,
) -> None:
    document = yaml.safe_load(CONTENT_MODEL.read_text(encoding="utf-8"))
    document["actions"][action_index]["guard"]["args"][guard_index] = {"bool": True}
    mutant = tmp_path / f"{mutant_name}.yaml"
    mutant.write_text(yaml.safe_dump(document, sort_keys=False), encoding="utf-8")
    verify = _verify(mutant)
    assert verify.returncode != 0, f"semantic mutant survived: {mutant_name}"
    report = json.loads(verify.stdout)
    assert report["ok"] is False
    assert report["report"]["failed_queries"] > 0


@pytest.mark.skipif(not ESSO_AVAILABLE, reason="ESSO is not available")
@pytest.mark.parametrize(
    ("guard_index", "mutant_name"),
    (
        (0, "qualification_parity_guard_removed"),
        (1, "qualification_application_completeness_guard_removed"),
        (2, "qualification_global_gap_guard_removed"),
        (3, "qualification_authority_guard_removed"),
    ),
)
def test_qualification_model_kills_every_promotion_guard_mutant(
    tmp_path: Path,
    guard_index: int,
    mutant_name: str,
) -> None:
    document = yaml.safe_load(QUALIFICATION_MODEL.read_text(encoding="utf-8"))
    document["actions"][0]["guard"]["args"][guard_index] = {"bool": True}
    mutant = tmp_path / f"{mutant_name}.yaml"
    mutant.write_text(yaml.safe_dump(document, sort_keys=False), encoding="utf-8")
    verify = _verify(mutant)
    assert verify.returncode != 0, f"semantic mutant survived: {mutant_name}"
    report = json.loads(verify.stdout)
    assert report["ok"] is False
    assert report["report"]["failed_queries"] > 0
