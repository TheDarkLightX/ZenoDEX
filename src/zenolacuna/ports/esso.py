"""Optional, capped ESSO invocation for the generated queue invariant model."""

from __future__ import annotations

import hashlib
import json
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

from src.integration.tau_runner import _run_subprocess_with_output_caps

from ..codec import encode
from ..model import Evidence, LacunaError
from ..queue_model import Admission, QueueAction, esso_model


@dataclass(frozen=True, slots=True)
class EssoQueueCheck:
    model_sha256: str
    evidence: Evidence
    code: str
    verified: bool | None
    failed_queries: tuple[str, ...]
    checked_queries: int
    esso_code_hash: str
    authority: str = "NONE"


def _unique(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise LacunaError("SOLVER_JSON_DUPLICATE")
        result[key] = value
    return result


def classify_esso(stdout: str, returncode: int, model_sha256: str) -> EssoQueueCheck:
    """Accept only an exact complete set of agreed Z3/CVC5 query outcomes."""
    unknown = EssoQueueCheck(model_sha256, Evidence.UNKNOWN, "SOLVER_UNKNOWN", None, (), 0, "")
    if returncode not in (0, 1):
        return unknown
    try:
        data = json.loads(stdout, object_pairs_hook=_unique)
        if type(data) is not dict or data.get("command") != "verify-multi":
            return unknown
        if data.get("solvers") != ["z3", "cvc5"] or type(data.get("ok")) is not bool:
            return unknown
        queries = data.get("queries")
        expected = {"init_implies_inv"} | {"inductive_" + action.value for action in QueueAction}
        if type(queries) is not dict or set(queries) != expected:
            return unknown
        failed: list[str] = []
        for name in sorted(expected):
            query = queries[name]
            if type(query) is not dict or query.get("agreed") is not True or query.get("needs_review") is not False:
                return unknown
            verdict = query.get("final_result")
            if verdict not in ("sat", "unsat"):
                return unknown
            for solver in ("z3", "cvc5"):
                row = query.get(solver)
                if type(row) is not dict or row.get("solver") != solver or row.get("error") is not None or row.get("result") != verdict:
                    return unknown
            if verdict == "sat":
                failed.append(name)
        verified = not failed
        if data["ok"] != verified or returncode != (0 if verified else 1):
            return unknown
        report = data.get("report")
        if type(report) is not dict or report.get("solvers_agreed") is not True:
            return unknown
        versions = report.get("tool_versions")
        if type(versions) is not dict or type(versions.get("esso_code_hash")) is not str:
            return unknown
        return EssoQueueCheck(model_sha256, Evidence.EXHAUSTIVE_FINITE,
                              "ESSO_INVARIANT_VERIFIED" if verified else "ESSO_COUNTEREXAMPLE",
                              verified, tuple(failed), len(expected), versions["esso_code_hash"])
    except (json.JSONDecodeError, LacunaError, ValueError, TypeError, RecursionError):
        return unknown


def verify_queue(root: Path, admission: Admission, *, timeout_seconds: int = 30) -> EssoQueueCheck:
    if type(timeout_seconds) is not int or not 1 <= timeout_seconds <= 60:
        raise LacunaError("INVALID_TIMEOUT")
    model = encode(esso_model(admission))
    model_sha = hashlib.sha256(model).hexdigest()
    with tempfile.TemporaryDirectory(prefix="zenolacuna-esso-") as directory:
        path = Path(directory) / "queue.yaml"
        path.write_bytes(model)
        command = [sys.executable, "-m", "ESSO", "verify-multi", str(path), "--solvers", "z3,cvc5"]
        returncode, stdout, _ = _run_subprocess_with_output_caps(
            command, input_text="", cwd=root, timeout_s=timeout_seconds,
            max_stdout_bytes=256_000, max_stderr_bytes=16_000,
        )
    return classify_esso(stdout, returncode, model_sha)
