"""Required native checks, with explicit tool selection and bounded subprocesses."""

import hashlib
import json
import sys
import tempfile
from pathlib import Path

from src.integration.tau_runner import _run_subprocess_with_output_caps
from src.tau_composition.runtime import TauQueryError, TauRuntime

from .codec import encode
from .model import LacunaError
from .ports.tau import compare
from .project_runtime import ExternalTools
from .project_types import ProjectState, plain

ESSO_BOOTSTRAP = """\
import importlib.util, pathlib, runpy, sys
package = pathlib.Path(sys.argv.pop(1)) / 'ESSO'
spec = importlib.util.spec_from_file_location('ESSO', package / '__init__.py',
                                            submodule_search_locations=[str(package)])
if spec is None or spec.loader is None:
    raise ImportError('ESSO package unavailable')
module = importlib.util.module_from_spec(spec)
sys.modules['ESSO'] = module
spec.loader.exec_module(module)
runpy.run_module('ESSO', run_name='__main__')
"""


def _unique(pairs: list[tuple[str, object]]) -> dict[str, object]:
    value: dict[str, object] = {}
    for key, item in pairs:
        if key in value:
            raise LacunaError("SOLVER_UNKNOWN")
        value[key] = item
    return value


def _classify(stdout: str, returncode: int, expected: set[str]) -> dict[str, object]:
    try:
        data = json.loads(stdout, object_pairs_hook=_unique)
    except (json.JSONDecodeError, ValueError, RecursionError) as exc:
        raise LacunaError("SOLVER_UNKNOWN") from exc
    if type(data) is not dict or data.get("command") != "verify-multi" or data.get("solvers") != ["z3", "cvc5"]:
        raise LacunaError("SOLVER_UNKNOWN")
    queries = data.get("queries")
    if type(queries) is not dict or set(queries) != expected:
        raise LacunaError("SOLVER_UNKNOWN")
    for name in sorted(expected):
        query = queries[name]
        if type(query) is not dict or query.get("agreed") is not True or query.get("needs_review") is not False:
            raise LacunaError("SOLVER_UNKNOWN")
        if query.get("final_result") not in ("sat", "unsat"):
            raise LacunaError("SOLVER_UNKNOWN")
        for solver in ("z3", "cvc5"):
            result = query.get(solver)
            if type(result) is not dict or result.get("solver") != solver or result.get("error") is not None:
                raise LacunaError("SOLVER_UNKNOWN")
            if result.get("result") != query["final_result"]:
                raise LacunaError("SOLVER_DISAGREEMENT")
    if any(queries[name]["final_result"] == "sat" for name in expected):
        raise LacunaError("ESSO_COUNTEREXAMPLE")
    if returncode != 0 or data.get("ok") is not True:
        raise LacunaError("SOLVER_UNKNOWN")
    report = data.get("report")
    if type(report) is not dict or report.get("solvers_agreed") is not True or type(report.get("tool_versions")) is not dict:
        raise LacunaError("SOLVER_UNKNOWN")
    return {"queries": tuple(sorted(expected)), "result": "unsat", "solvers": ("z3", "cvc5"),
            "tool_versions": report["tool_versions"]}


def _esso(state: ProjectState, tools: ExternalTools) -> dict[str, object]:
    from .ports.signal_graph_esso import signal_graph_esso_model, verify_signal_graph_esso
    from .project_bindings import esso_fingerprint
    from .signal_migration import CandidateMode, migration_candidate

    if tools.esso_root is None:
        raise LacunaError("SOLVER_UNKNOWN:ESSO_MISSING")
    if esso_fingerprint(tools.esso_root) != state.task.esso_sha256:
        raise LacunaError("SOLVER_SOURCE_DRIFT")
    matched = [mode for mode in CandidateMode if state.candidate == migration_candidate(mode)]
    if len(matched) != 1:
        raise LacunaError("UNALLOWLISTED_SOURCE")
    mode = matched[0]
    model = signal_graph_esso_model(mode, state.task.runtime.inputs)
    parity = verify_signal_graph_esso(model, mode, state.task.runtime.inputs)
    # This independent finite gate checks the supplied IR, including guards and
    # all transitions, before any solver can establish its invariant claim.
    if not parity.verified:
        raise LacunaError("ESSO_RUNTIME_MISMATCH")
    raw = encode(model)
    actions = model.get("actions")
    if type(actions) is not list:
        raise LacunaError("ESSO_RUNTIME_MISMATCH")
    expected = {"init_implies_inv"} | {"inductive_" + action["id"] for action in actions}
    if len(expected) > 64:
        raise LacunaError("SOLVER_QUERY_LIMIT")
    # Select only the pinned ESSO package. Its checkout root must not enter
    # sys.path: an unpinned sibling z3.py could replace the installed solver.
    with tempfile.TemporaryDirectory(prefix="zenolacuna-project-esso-") as directory:
        path = Path(directory) / "model.yaml"
        path.write_bytes(raw)
        command = [sys.executable, "-I", "-B", "-X", f"pycache_prefix={Path(directory) / 'pycache'}",
                   "-c", ESSO_BOOTSTRAP, str(tools.esso_root.resolve()),
                   "verify-multi", str(path), "--solvers", "z3,cvc5"]
        rc, stdout, _stderr = _run_subprocess_with_output_caps(
            command, input_text="", cwd=Path(directory), timeout_s=60,
            max_stdout_bytes=512_000, max_stderr_bytes=32_000,
        )
    if esso_fingerprint(tools.esso_root) != state.task.esso_sha256:
        raise LacunaError("SOLVER_SOURCE_DRIFT")
    result = _classify(stdout, rc, expected)
    return {**result, "code": "ESSO_GRAPH_VERIFIED", "model_sha256": hashlib.sha256(raw).hexdigest(),
            "esso_sha256": state.task.esso_sha256, "parity": plain(parity)}


def check_required_tools(state: ProjectState, tools: ExternalTools) -> dict[str, object]:
    results: dict[str, object] = {}
    if state.task.tau_sha256 is not None:
        if tools.tau_bin is None:
            raise LacunaError("SOLVER_UNKNOWN:TAU_MISSING")
        try:
            runtime = TauRuntime(tools.tau_bin, timeout_seconds=15)
            if runtime.binary_sha256 != state.task.tau_sha256:
                raise LacunaError("SOLVER_SOURCE_DRIFT")
            if state.candidate is None or not state.survivors:
                raise LacunaError("CANDIDATE_REQUIRED")
            # Refinement includes mandatory positive behavior; model closure has
            # already checked it. Equality cross-check is required for this Tau
            # profile; a strict refinement can use the Python-only profile.
            result = compare(runtime, state.task.scope, state.candidate.allowed,
                             state.task.scope.hypotheses[state.survivors[0]].allowed)
            if result.equivalent is not True:
                raise LacunaError("SOLVER_UNKNOWN" if result.equivalent is None else "TAU_RELATION_MISMATCH")
            runtime.check_subject()
            results["tau"] = plain(result)
            if state.task.runtime.adapter == "SIGNAL_MIGRATION":
                from .ports.migration_tau import project_consumer_guard
                results["tau_migration_guard"] = project_consumer_guard(runtime)
                runtime.check_subject()
        except (TauQueryError, OSError, ValueError) as exc:
            if isinstance(exc, LacunaError):
                raise
            raise LacunaError("SOLVER_UNKNOWN:TAU_FAILURE") from exc
    if state.task.esso_sha256 is not None:
        results["esso"] = _esso(state, tools)
    return results
