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
STATE_BINDING_MODEL = (
    ROOT / "src" / "kernels" / "dex" / "fcis_fee_configuration_state_binding_v2.yaml"
)
OCCURRENCE_MODEL = (
    ROOT / "src" / "kernels" / "dex" / "zusd_authenticated_borrow_fee_occurrence_v1.yaml"
)
COMPOSITION_MODEL = (
    ROOT / "src" / "kernels" / "dex" / "zusd_state_bound_fee_accrual_allocation_v2.yaml"
)
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
@pytest.mark.parametrize(
    "model",
    (STATE_BINDING_MODEL, OCCURRENCE_MODEL, COMPOSITION_MODEL),
)
def test_esso_fee_source_binding_models_verify(model: Path) -> None:
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
    assert report["report"]["failed_queries"] == 0


@pytest.mark.skipif(not ESSO_AVAILABLE, reason="ESSO is not available")
@pytest.mark.parametrize(
    ("guard_index", "mutant_name"),
    (
        (0, "state_projection_guard_removed"),
        (1, "configuration_guard_removed"),
        (2, "configuration_root_guard_removed"),
        (3, "deployment_guard_removed"),
        (4, "activation_guard_removed"),
    ),
)
def test_esso_state_binding_kills_guard_mutants(
    tmp_path: Path,
    guard_index: int,
    mutant_name: str,
) -> None:
    document = yaml.safe_load(STATE_BINDING_MODEL.read_text(encoding="utf-8"))
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
    ("guard_index", "mutant_name"),
    (
        (0, "identity_guard_removed"),
        (1, "command_family_guard_removed"),
        (2, "pre_state_guard_removed"),
        (3, "command_root_guard_removed"),
        (4, "kernel_accept_guard_removed"),
        (5, "debt_delta_guard_removed"),
    ),
)
def test_esso_occurrence_kills_guard_mutants(
    tmp_path: Path,
    guard_index: int,
    mutant_name: str,
) -> None:
    document = yaml.safe_load(OCCURRENCE_MODEL.read_text(encoding="utf-8"))
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
        (1, "free_debt", "free_debt_update_removed"),
        (2, "issued_principal", "principal_update_removed"),
        (3, "protocol_fee", "protocol_fee_update_removed"),
        (4, "occurrence_total", "occurrence_update_removed"),
    ),
)
def test_esso_occurrence_kills_update_mutants(
    tmp_path: Path,
    update_index: int,
    state_var: str,
    mutant_name: str,
) -> None:
    document = yaml.safe_load(OCCURRENCE_MODEL.read_text(encoding="utf-8"))
    document["actions"][0]["updates"][update_index]["expr"] = {"var": state_var}
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
        (0, "controlled_sources_guard_removed"),
        (1, "request_context_guard_removed"),
        (2, "zusd_state_guard_removed"),
        (3, "component_roots_guard_removed"),
        (4, "managed_identity_guard_removed"),
        (5, "fee_domain_guard_removed"),
        (6, "cumulative_history_guard_removed"),
        (7, "allocation_guard_removed"),
    ),
)
def test_esso_composition_kills_guard_mutants(
    tmp_path: Path,
    guard_index: int,
    mutant_name: str,
) -> None:
    document = yaml.safe_load(COMPOSITION_MODEL.read_text(encoding="utf-8"))
    document["actions"][0]["guard"]["args"][guard_index] = {"bool": True}
    mutant = tmp_path / f"{mutant_name}.yaml"
    mutant.write_text(yaml.safe_dump(document, sort_keys=False), encoding="utf-8")

    verify = _verify(mutant)
    assert verify.returncode != 0, f"semantic mutant survived: {mutant_name}"
    report = json.loads(verify.stdout)
    assert report["ok"] is False
    assert report["report"]["failed_queries"] > 0
