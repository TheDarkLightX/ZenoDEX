import json
from dataclasses import asdict

import pytest

from src.zenolacuna.model import Evidence
from src.zenolacuna.ports.esso import classify_esso
from src.zenolacuna.queue_model import QueueAction


def solver_result() -> dict:
    names = ["init_implies_inv"] + ["inductive_" + a.value for a in QueueAction]
    return {
        "command": "verify-multi", "solvers": ["z3", "cvc5"], "ok": True,
        "queries": {name: {
            "agreed": True, "needs_review": False, "final_result": "unsat",
            "z3": {"solver": "z3", "result": "unsat", "error": None},
            "cvc5": {"solver": "cvc5", "result": "unsat", "error": None},
        } for name in names},
        "report": {"solvers_agreed": True, "tool_versions": {"esso_code_hash": "test-fixture"}},
    }


@pytest.mark.parametrize("fault", ("missing", "unknown", "error", "disagree", "nonzero", "malformed", "duplicate"))
def test_solver_fault_never_becomes_invariant_evidence(fault: str) -> None:
    value = solver_result()
    row = value["queries"]["inductive_enqueue"]
    returncode = 0
    if fault == "missing":
        del value["queries"]["init_implies_inv"]
    elif fault == "unknown":
        row["final_result"] = "unknown"
    elif fault == "error":
        row["z3"]["error"] = "timeout"
    elif fault == "disagree":
        row["cvc5"]["result"] = "sat"
    elif fault == "nonzero":
        returncode = 1
    encoded = json.dumps(value)
    if fault == "malformed":
        encoded += "extra"
    if fault == "duplicate":
        encoded = encoded.replace('"ok": true', '"ok": false,"ok": true')
    result = classify_esso(encoded, returncode, "0" * 64)
    assert result.evidence is Evidence.UNKNOWN and result.verified is None
    assert asdict(result)["authority"] == "NONE"


def test_all_named_obligations_require_two_agreeing_solvers() -> None:
    result = classify_esso(json.dumps(solver_result()), 0, "0" * 64)
    assert result.code == "ESSO_INVARIANT_VERIFIED" and result.verified is True
    assert result.checked_queries == 9
