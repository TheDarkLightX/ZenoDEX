"""Dual-solver, registry-parity, and guard-mutant tests for content projection."""

from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any, Callable

import pytest
import yaml

from src.core.fcis_m6_global_state_projection_v1 import (
    M6_KNOWN_GLOBAL_PROJECTION_GAPS_V1,
    M6_PROJECTION_AUTHORITY_OBLIGATIONS_V1,
    M6_REQUIRED_APPLICATION_STATE_COMPONENTS_V1,
    M6_ZENO_LEDGER_SPOT_COMMITTED_COMPONENTS_V1,
)
from src.integration.fcis_m6_tau_zenoledger_projection_v1 import (
    M6_DEX_SNAPSHOT_FIELD_COMPONENTS_V1,
    M6_DEX_SNAPSHOT_REPRESENTATION_ONLY_FIELDS_V1,
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


def _action(document: dict[str, Any], action_id: str) -> dict[str, Any]:
    actions = document["actions"]
    assert isinstance(actions, list)
    matches = [action for action in actions if action["id"] == action_id]
    assert len(matches) == 1
    return matches[0]


def _reachable_states_and_actions(
    model: Path,
) -> tuple[list[dict[str, int]], set[str]]:
    from ESSO.ir.schema import CandidateIR
    from ESSO.kernel.interpreter import StepOk, prepare_step_context, step_ctx
    from ESSO.verify.lts_minimize import (
        LtsMinimizeConfig,
        _enumerate_commands,
        _enumerate_reachable_states,
    )

    ir = CandidateIR.from_json_dict(
        yaml.safe_load(model.read_text(encoding="utf-8")),
        path=str(model),
    ).canonicalized()
    config = LtsMinimizeConfig(scope="reachable", max_states=2_000)
    commands = _enumerate_commands(ir, cfg=config)
    assert isinstance(commands, list)
    states = _enumerate_reachable_states(ir, cfg=config, cmds=commands)
    assert isinstance(states, list)
    context = prepare_step_context(ir)
    enabled = {
        command.tag
        for state in states
        for command in commands
        if isinstance(step_ctx(state, command, context), StepOk)
    }
    return states, enabled


def test_formal_metadata_matches_every_runtime_closed_registry() -> None:
    content = yaml.safe_load(CONTENT_MODEL.read_text(encoding="utf-8"))
    qualification = yaml.safe_load(QUALIFICATION_MODEL.read_text(encoding="utf-8"))
    assert content["meta"]["component_registry"] == [
        component.value for component in M6_REQUIRED_APPLICATION_STATE_COMPONENTS_V1
    ]
    assert content["meta"]["zeno_ledger_spot_committed_components"] == [
        component.value for component in M6_ZENO_LEDGER_SPOT_COMMITTED_COMPONENTS_V1
    ]
    assert content["meta"]["dex_snapshot_field_registry"] == [
        *(
            {"field": field, "classification": "representation_only"}
            for field in M6_DEX_SNAPSHOT_REPRESENTATION_ONLY_FIELDS_V1
        ),
        *(
            {"field": field, "component": component.value}
            for field, component in M6_DEX_SNAPSHOT_FIELD_COMPONENTS_V1
        ),
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
    content = yaml.safe_load(CONTENT_MODEL.read_text(encoding="utf-8"))
    content["meta"]["zeno_ledger_spot_committed_components"].pop()
    assert content["meta"]["zeno_ledger_spot_committed_components"] != [
        component.value for component in M6_ZENO_LEDGER_SPOT_COMMITTED_COMPONENTS_V1
    ]
    content = yaml.safe_load(CONTENT_MODEL.read_text(encoding="utf-8"))
    content["meta"]["dex_snapshot_field_registry"].pop()
    assert len(content["meta"]["dex_snapshot_field_registry"]) != (
        len(M6_DEX_SNAPSHOT_FIELD_COMPONENTS_V1)
        + len(M6_DEX_SNAPSHOT_REPRESENTATION_ONLY_FIELDS_V1)
    )


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
    ("action_id", "guard_index", "mutant_name"),
    (
        ("admit_tau_content", 0, "tau_canonical_guard_removed"),
        ("admit_tau_content", 1, "tau_commitment_guard_removed"),
        ("admit_tau_content", 2, "tau_component_derivation_guard_removed"),
        ("admit_tau_content", 3, "tau_coverage_guard_removed"),
        ("admit_tau_content", 4, "tau_registry_guard_removed"),
        ("admit_ledger_content", 0, "ledger_header_body_guard_removed"),
        ("admit_ledger_content", 1, "ledger_post_state_guard_removed"),
        ("admit_ledger_content", 2, "ledger_component_derivation_guard_removed"),
        ("admit_ledger_content", 3, "ledger_coverage_guard_removed"),
        ("admit_ledger_content", 4, "ledger_registry_guard_removed"),
        ("issue_content_parity", 0, "parity_tau_admission_guard_removed"),
        ("issue_content_parity", 1, "parity_ledger_admission_guard_removed"),
        ("issue_content_parity", 2, "parity_source_kind_guard_removed"),
        ("issue_content_parity", 3, "parity_content_equality_guard_removed"),
    ),
)
def test_content_model_kills_every_admission_guard_mutant(
    tmp_path: Path,
    action_id: str,
    guard_index: int,
    mutant_name: str,
) -> None:
    document = yaml.safe_load(CONTENT_MODEL.read_text(encoding="utf-8"))
    _action(document, action_id)["guard"]["args"][guard_index] = {"bool": True}
    mutant = tmp_path / f"{mutant_name}.yaml"
    mutant.write_text(yaml.safe_dump(document, sort_keys=False), encoding="utf-8")
    verify = _verify(mutant)
    assert verify.returncode != 0, f"semantic mutant survived: {mutant_name}"
    report = json.loads(verify.stdout)
    assert report["ok"] is False
    assert report["report"]["failed_queries"] > 0


@pytest.mark.skipif(not ESSO_AVAILABLE, reason="ESSO is not available")
@pytest.mark.parametrize(
    "action_id",
    (
        "invalidate_tau_source_canonical",
        "invalidate_tau_commitment",
        "invalidate_ledger_header_body",
        "invalidate_ledger_post_state",
        "invalidate_component_derivation",
        "invalidate_coverage_partition",
        "invalidate_registry_binding",
        "invalidate_source_kinds",
        "invalidate_content_equality",
    ),
)
def test_content_model_freezes_every_admission_premise_after_admission(
    tmp_path: Path,
    action_id: str,
) -> None:
    document = yaml.safe_load(CONTENT_MODEL.read_text(encoding="utf-8"))
    _action(document, action_id)["guard"] = {"bool": True}
    mutant = tmp_path / f"{action_id}_post_admission_mutant.yaml"
    mutant.write_text(yaml.safe_dump(document, sort_keys=False), encoding="utf-8")
    verify = _verify(mutant)
    assert verify.returncode != 0, f"semantic mutant survived: {action_id}"
    report = json.loads(verify.stdout)
    assert report["ok"] is False
    assert report["report"]["failed_queries"] > 0


@pytest.mark.skipif(not ESSO_AVAILABLE, reason="ESSO is not available")
def test_intended_projection_and_rejection_actions_are_reachable() -> None:
    content_states, content_actions = _reachable_states_and_actions(CONTENT_MODEL)
    assert {
        "admit_tau_content",
        "admit_ledger_content",
        "issue_content_parity",
    } <= content_actions
    assert any(state["parity_issued"] == 1 for state in content_states)

    qualification_states, qualification_actions = _reachable_states_and_actions(QUALIFICATION_MODEL)
    assert {
        "reject_current_content_receipt",
        "invalidate_content_parity",
        "reject_invalid_content_receipt",
    } <= qualification_actions
    assert any(
        state["rejection_issued"] == 1 and state["authority_issued"] == 0
        for state in qualification_states
    )
    assert all(state["authority_issued"] == 0 for state in qualification_states)


@pytest.mark.skipif(not ESSO_AVAILABLE, reason="ESSO is not available")
@pytest.mark.parametrize(
    ("action_id", "postcondition"),
    (
        ("admit_tau_content", lambda state: state["tau_admitted"] == 1),
        ("admit_ledger_content", lambda state: state["ledger_admitted"] == 1),
        ("issue_content_parity", lambda state: state["parity_issued"] == 1),
    ),
)
def test_content_progress_update_mutant_is_killed_by_reachability(
    tmp_path: Path,
    action_id: str,
    postcondition: Callable[[dict[str, int]], bool],
) -> None:
    document = yaml.safe_load(CONTENT_MODEL.read_text(encoding="utf-8"))
    update = _action(document, action_id)["updates"][0]
    update["expr"] = {"const": 0}
    mutant = tmp_path / f"{action_id}_no_progress.yaml"
    mutant.write_text(yaml.safe_dump(document, sort_keys=False), encoding="utf-8")
    states, _actions = _reachable_states_and_actions(mutant)
    assert not any(postcondition(state) for state in states)


@pytest.mark.skipif(not ESSO_AVAILABLE, reason="ESSO is not available")
@pytest.mark.parametrize(
    "action_id",
    ("reject_current_content_receipt", "reject_invalid_content_receipt"),
)
def test_qualification_rejection_update_mutant_is_killed_by_reachability(
    tmp_path: Path,
    action_id: str,
) -> None:
    document = yaml.safe_load(QUALIFICATION_MODEL.read_text(encoding="utf-8"))
    _action(document, action_id)["updates"][0]["expr"] = {"const": 0}
    mutant = tmp_path / f"{action_id}_no_rejection.yaml"
    mutant.write_text(yaml.safe_dump(document, sort_keys=False), encoding="utf-8")
    states, _actions = _reachable_states_and_actions(mutant)
    if action_id == "reject_current_content_receipt":
        assert not any(
            state["content_parity_admitted"] == 1 and state["rejection_issued"] == 1
            for state in states
        )
    else:
        assert not any(
            state["content_parity_admitted"] == 0 and state["rejection_issued"] == 1
            for state in states
        )


@pytest.mark.skipif(not ESSO_AVAILABLE, reason="ESSO is not available")
@pytest.mark.parametrize(
    "mutant_name",
    (
        "authority_enabled_action",
        "authority_enabled_initially",
        "current_rejection_replaced_by_authority",
        "invalid_rejection_replaced_by_authority",
    ),
)
def test_qualification_model_kills_every_authority_issue_mutant(
    tmp_path: Path,
    mutant_name: str,
) -> None:
    document = yaml.safe_load(QUALIFICATION_MODEL.read_text(encoding="utf-8"))
    if mutant_name == "authority_enabled_action":
        document["actions"].append(
            {
                "id": "issue_authority_mutant",
                "params": [],
                "guard": {"bool": True},
                "updates": [{"var": "authority_issued", "expr": {"const": 1}}],
                "effects": {},
            }
        )
    elif mutant_name == "authority_enabled_initially":
        next(item for item in document["init"] if item["var"] == "authority_issued")["expr"] = {
            "const": 1
        }
    else:
        action_id = (
            "reject_current_content_receipt"
            if mutant_name == "current_rejection_replaced_by_authority"
            else "reject_invalid_content_receipt"
        )
        update = _action(document, action_id)["updates"][0]
        update["var"] = "authority_issued"
    mutant = tmp_path / f"{mutant_name}.yaml"
    mutant.write_text(yaml.safe_dump(document, sort_keys=False), encoding="utf-8")
    verify = _verify(mutant)
    assert verify.returncode != 0, f"semantic mutant survived: {mutant_name}"
    report = json.loads(verify.stdout)
    assert report["ok"] is False
    assert report["report"]["failed_queries"] > 0
