#!/usr/bin/env python3
"""Replay SMT checks for the ZenoOracle freshness guard."""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
CONTRACT_PATH = ROOT / "formal" / "tau" / "contracts" / "oracle_freshness_v2.contract.json"
SCHEMA = "zenodex.oracle.smt_freshness_replay.v1"


QUERY_TEMPLATE = """(set-logic QF_BV)
(declare-fun i1 () (_ BitVec 32))
(declare-fun i2 () (_ BitVec 32))
(declare-fun i3 () (_ BitVec 32))
(declare-fun i4 () (_ BitVec 32))
(declare-fun i5 () (_ BitVec 32))
(define-fun params_ok () Bool
  (and (bvugt i3 (_ bv0 32)) (bvugt i4 (_ bv0 32)) (bvuge i2 i1)))
(define-fun freshness_ok () Bool
  (and params_ok (bvule (bvsub i2 i1) i3)))
(define-fun monotonic_jump_ok () Bool
  (and (bvugt i1 i5) (bvule (bvsub i1 i5) i4)))
(define-fun oracle_valid () Bool
  (and freshness_ok monotonic_jump_ok))
{assertion}
(check-sat)
"""


CASES = [
    {
        "id": "future_oracle_timestamp_rejected",
        "assertion": "(assert (and oracle_valid (not (bvuge i2 i1))))",
        "expected": "unsat",
    },
    {
        "id": "stale_oracle_timestamp_rejected",
        "assertion": "(assert (and oracle_valid (not (bvule (bvsub i2 i1) i3))))",
        "expected": "unsat",
    },
    {
        "id": "zero_staleness_bound_rejected",
        "assertion": "(assert (and oracle_valid (= i3 (_ bv0 32))))",
        "expected": "unsat",
    },
    {
        "id": "zero_jump_bound_rejected",
        "assertion": "(assert (and oracle_valid (= i4 (_ bv0 32))))",
        "expected": "unsat",
    },
    {
        "id": "non_monotonic_oracle_timestamp_rejected",
        "assertion": "(assert (and oracle_valid (not (bvugt i1 i5))))",
        "expected": "unsat",
    },
    {
        "id": "excessive_oracle_jump_rejected",
        "assertion": "(assert (and oracle_valid (not (bvule (bvsub i1 i5) i4))))",
        "expected": "unsat",
    },
]


def _query(assertion: str) -> str:
    return QUERY_TEMPLATE.format(assertion=assertion)


def _run_solver(solver: str, query: str, tmp_dir: Path) -> dict[str, Any]:
    exe = shutil.which(solver)
    if exe is None:
        return {"solver": solver, "ok": False, "status": "missing", "stdout": "", "stderr": ""}
    query_path = tmp_dir / f"query_{solver}.smt2"
    query_path.write_text(query, encoding="utf-8")
    if solver == "z3":
        cmd = [exe, "-smt2", str(query_path)]
    elif solver == "cvc5":
        cmd = [exe, "--lang", "smt2", str(query_path)]
    else:  # pragma: no cover
        raise ValueError(f"unsupported_solver:{solver}")
    proc = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, check=False, timeout=10)
    stdout = (proc.stdout or "").strip()
    status = stdout.splitlines()[0].strip() if stdout else ""
    return {
        "solver": solver,
        "ok": proc.returncode == 0 and status in {"sat", "unsat"},
        "status": status,
        "returncode": proc.returncode,
        "stdout": stdout,
        "stderr": (proc.stderr or "").strip(),
    }


def _contract_ok() -> tuple[bool, list[str]]:
    errors: list[str] = []
    try:
        contract = json.loads(CONTRACT_PATH.read_text(encoding="utf-8"))
    except Exception as exc:
        return False, [f"contract_load_failed:{exc}"]
    if contract.get("spec_id") != "oracle_freshness_v2":
        errors.append("contract_spec_id_mismatch")
    if contract.get("proof_scope") != "bounded_assurance_domain":
        errors.append("contract_proof_scope_mismatch")
    theorem_ids = {
        str(row.get("id", ""))
        for row in contract.get("theorems", [])
        if isinstance(row, dict)
    }
    for theorem_id in {"o1_exact", "o2_exact", "o4_sound_complete"}:
        if theorem_id not in theorem_ids:
            errors.append(f"contract_missing_theorem:{theorem_id}")
    return not errors, errors


def build_status() -> dict[str, Any]:
    contract_ok, contract_errors = _contract_ok()
    case_rows: list[dict[str, Any]] = []
    with tempfile.TemporaryDirectory(prefix="zeno-oracle-smt-freshness-") as tmp:
        tmp_dir = Path(tmp)
        for case in CASES:
            query = _query(str(case["assertion"]))
            solver_rows = [_run_solver(solver, query, tmp_dir) for solver in ("z3", "cvc5")]
            expected = str(case["expected"])
            ok = all(row["ok"] and row["status"] == expected for row in solver_rows)
            case_rows.append(
                {
                    "id": case["id"],
                    "ok": ok,
                    "expected": expected,
                    "solvers": solver_rows,
                }
            )
    failed = [case for case in case_rows if not case["ok"]]
    return {
        "schema": SCHEMA,
        "ok": contract_ok and not failed,
        "status": "accepted" if contract_ok and not failed else "rejected",
        "contract_path": "formal/tau/contracts/oracle_freshness_v2.contract.json",
        "contract_ok": contract_ok,
        "contract_errors": contract_errors,
        "case_count": len(case_rows),
        "failed_count": len(failed),
        "cases": case_rows,
        "non_claims": [
            "does_not_claim_tau_binary_equivalence",
            "does_not_claim_unbounded_temporal_liveness",
            "does_not_claim_production_oracle_truth",
        ],
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--format", choices=("json", "text"), default="json")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    status = build_status()
    if args.format == "json":
        sys.stdout.write(json.dumps(status, indent=2, sort_keys=True) + "\n")
    else:
        sys.stdout.write(
            "\n".join(
                [
                    f"case_count = {status['case_count']}",
                    f"failed_count = {status['failed_count']}",
                    f"status = {status['status']}",
                ]
            )
            + "\n"
        )
    return 0 if status["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
