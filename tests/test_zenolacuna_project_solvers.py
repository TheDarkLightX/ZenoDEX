"""Required solver failures and disagreement cannot mint persisted completion."""

import hashlib
import json
import os
import subprocess
import sys
from dataclasses import replace
from pathlib import Path

import pytest

from src.tau_composition.runtime import TauRuntime
from src.zenolacuna.model import LacunaError
from src.zenolacuna.ports.migration_tau import project_consumer_guard
from src.zenolacuna.project_runtime import ExternalTools
from src.zenolacuna.project_solvers import ESSO_BOOTSTRAP, _classify
from tests.test_zenolacuna_project_evidence import _create, _pipeline_assess, _pipeline_task


@pytest.mark.parametrize("script", (
    b"#!/bin/sh\nprintf 'malformed verdict\\n'\n",
    b"#!/bin/sh\nprintf '%%1: F\\n'\n",
    b"#!/bin/sh\nprintf '%%1: T\\n'\nexit 7\n",
))
def test_given_failed_or_disagreeing_native_tau_when_signed_completion_applied_then_no_effect(tmp_path, script):
    binary = tmp_path / "fixture-tau"
    binary.write_bytes(script)
    binary.chmod(0o700)
    task = replace(_pipeline_task(tmp_path), tau_sha256=hashlib.sha256(script).hexdigest())
    project = _create(tmp_path, task)
    project.tools = ExternalTools(tau_bin=binary)
    request = _pipeline_assess(project)
    before = project.export_bytes()
    with pytest.raises(LacunaError, match="^SOLVER_UNKNOWN"):
        project.apply(request)
    assert project.export_bytes() == before
    assert project.state().completion is None


def test_given_external_deadline_when_complete_runs_then_timeout_cannot_be_logical_false(tmp_path, monkeypatch):
    task = replace(_pipeline_task(tmp_path), tau_sha256=hashlib.sha256(Path("/bin/true").read_bytes()).hexdigest())
    project = _create(tmp_path, task)
    project.tools = ExternalTools(tau_bin=Path("/bin/true"))
    request = _pipeline_assess(project)
    before = project.export_bytes()
    monkeypatch.setattr("src.tau_composition.runtime._run_subprocess_with_output_caps",
                        lambda *_args, **_kwargs: (-1, "", "tau timed out"))
    with pytest.raises(LacunaError, match="^SOLVER_UNKNOWN"):
        project.apply(request)
    assert project.export_bytes() == before


def _esso_answer():
    names = ("init_implies_inv", "inductive_upgrade_consumer")
    data = {"command": "verify-multi", "solvers": ["z3", "cvc5"], "ok": True,
            "queries": {}, "report": {"solvers_agreed": True, "tool_versions": {}}}
    for name in names:
        data["queries"][name] = {
            "agreed": True, "needs_review": False, "final_result": "unsat",
            **{s: {"solver": s, "error": None, "result": "unsat"} for s in ("z3", "cvc5")},
        }
    return data, set(names)


@pytest.mark.parametrize("fault", ("missing-query", "extra-query", "unknown", "disagree", "error", "failed-exit", "duplicate-key"))
def test_given_incomplete_native_esso_result_when_classified_then_no_proof(fault):
    value, expected = _esso_answer()
    query = value["queries"]["init_implies_inv"]
    rc = 0
    if fault == "missing-query":
        del value["queries"]["init_implies_inv"]
    elif fault == "extra-query":
        value["queries"]["inductive_unmodeled"] = query
    elif fault == "unknown":
        query["final_result"] = "unknown"
    elif fault == "disagree":
        query["cvc5"]["result"] = "sat"
    elif fault == "error":
        query["z3"]["error"] = "timeout"
    elif fault == "failed-exit":
        rc = -1
    raw = json.dumps(value)
    if fault == "duplicate-key":
        raw = raw[:-1] + ',"ok":true}'
    with pytest.raises(LacunaError, match="^SOLVER_(UNKNOWN|DISAGREEMENT)$"):
        _classify(raw, rc, expected)


def test_given_all_named_esso_obligations_when_both_solvers_agree_then_exact_set_returned():
    value, expected = _esso_answer()
    report = _classify(json.dumps(value), 0, expected)
    assert report["queries"] == tuple(sorted(expected))
    assert report["result"] == "unsat"


def test_given_native_tau_when_migration_preimage_derived_then_all_capability_states_match():
    binary = os.environ.get("TAU_BIN")
    if binary is None:
        pytest.skip("Set TAU_BIN to a separately installed Tau executable")
    result = project_consumer_guard(TauRuntime(binary))
    assert result["code"] == "TAU_CONSUMER_GUARD_PROJECTED"
    assert result["checked_capability_states"] == 18
    assert result["authority"] == "NONE"


def test_given_solver_disagreement_when_migration_guard_projected_then_no_certificate():
    class DisagreeingTau:
        binary_sha256 = "0" * 64

        def project(self, _formula):
            return "T"

        def valid(self, _formula):
            return False

    with pytest.raises(LacunaError, match="^SOLVER_DISAGREEMENT$"):
        project_consumer_guard(DisagreeingTau())


def test_given_esso_root_sibling_when_native_child_imports_z3_then_only_pinned_installation_runs(tmp_path):
    import importlib.util
    installed = importlib.util.find_spec("z3")
    if installed is None:
        pytest.skip("Native ESSO profile requires installed Z3")
    package = tmp_path / "ESSO"
    package.mkdir()
    (package / "__init__.py").write_text("")
    (package / "__main__.py").write_text("import z3\nprint(z3.__file__)\n")
    (tmp_path / "z3.py").write_text("# This sibling is outside the ESSO package fingerprint.\n")
    result = subprocess.run([sys.executable, "-I", "-B", "-X", f"pycache_prefix={tmp_path / 'fresh-cache'}",
                             "-c", ESSO_BOOTSTRAP, str(tmp_path)],
                            cwd=tmp_path, capture_output=True, text=True, check=False, timeout=15)
    assert result.returncode == 0, result.stderr
    assert Path(result.stdout.strip()).resolve() == Path(installed.origin).resolve()
