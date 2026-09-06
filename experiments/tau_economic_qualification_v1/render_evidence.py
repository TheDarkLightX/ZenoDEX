"""Render the source-pinned hygiene packet for this bounded research slice.

Run ``python3 -B -m experiments.tau_economic_qualification_v1.render_evidence``
after the four focused test files pass. Rendering declares evidence paths; it
does not execute tests, the solver or Tau, and cannot promote their results.
"""

from __future__ import annotations

import ast
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PACKAGE = "experiments/tau_economic_qualification_v1/"
SOURCES = tuple(PACKAGE + name + ".py" for name in (
    "reference", "runner", "qualify", "conservation_equivalence", "render_evidence",
)) + tuple("src/tau_specs/recommended/" + name + ".tau" for name in (
    "nonce_replay_guard_v1", "nonce_manager_v1", "transfer_hook_guard_v1", "zusd_transfer_guard_v1",
)) + ("src/integration/tau_runner.py", "experiments/tau_adt_rows_v1/execution.py")
TESTS = tuple("tests/tau/" + name + ".py" for name in (
    "test_tau_economic_reference_v1", "test_tau_economic_runner_v1",
    "test_tau_economic_qualification_v1", "test_tau_transfer_conservation_equivalence_v1",
))
EVIDENCE_ID = "THV1-20260905-tau-economic-qualification-v1"


def main() -> int:
    source_pins = [{"path": path, "sha256": hashlib.sha256((ROOT / path).read_bytes()).hexdigest()}
                   for path in SOURCES]
    test_pins = []
    for path in TESTS:
        data = (ROOT / path).read_bytes()
        nodes = [f"{path}::{node.name}" for node in ast.parse(data).body
                 if isinstance(node, ast.FunctionDef) and node.name.startswith("test_")]
        if not nodes:
            raise ValueError(f"no test nodes: {path}")
        test_pins.append({"path": path, "sha256": hashlib.sha256(data).hexdigest(), "node_ids": nodes})
    packet = {
        "schema": "zenodex/test-hygiene-evidence/v1", "evidence_id": EVIDENCE_ID,
        "created_date": "2026-09-05", "change_kind": "assurance_infrastructure", "risk_class": "assurance",
        "claim_scope": "Bounded current-Tau economic predicate replay: all observed output fields, independent fixed and generated vectors, caller-state nonce histories, and one manually translated full-bv32 optimization equivalence proof. Experimental only; no ownership or publication authority.",
        "invariant_ids": ["TAU-COMPLETE-OUTPUT-TRACE", "TAU-EXACT-SOURCE-AND-STREAM-BINDING",
                          "TAU-FAILED-RUN-NO-PASS-PROMOTION", "TAU-TRANSFER-DELTA-CONSERVATION-EQUIVALENCE"],
        "failure_modes": ["missing or reordered outputs", "selected gate hides an incorrect standalone field",
                          "unproved solver result promoted", "stale caller nonce mistaken for persistent replay protection",
                          "final report failure preserves an old success after execution"],
        "source_pins": source_pins, "test_pins": test_pins, "removed_paths": [],
        "evidence_families": ["negative_regression", "boundary", "differential", "stateful", "formal"],
        "aaa": {"status": "applied", "reason": "Arrange exact source and fixed observations, execute the pure checker or solver, and compare every declared output and failure disposition."},
        "reject_is_noop": {"status": "not_applicable", "reason": "This research shell has no ledger mutation port. Its report is deliberately replaced on rejection. Caller-state nonce histories separately require no simulated nonce update on denied rows."},
        "boundary_dimensions": [
            {"name": "unsigned arithmetic", "points": ["zero and one", "uint32 maximum and neighbors", "signed comparison seam", "modular sum and delta wrap"]},
            {"name": "nonce lifecycle", "points": ["gap 999, 1000 and 1001", "replay and recovery", "maximum nonce exhaustion", "stale caller-state repetition"]},
            {"name": "transcript and report", "points": ["one to eight rows", "missing or extra outputs", "nonzero exit and diagnostic text", "initial and final report write failures"]},
        ],
        "mutations": [],
        "nonclaims": [
            "Rendering this packet does not execute its named tests, the explicit Tau CLI or the independent solver replay.",
            "Unit tests need no Tau executable; the separate qualification CLI must be run and checked for actual-engine evidence.",
            "No authenticated ownership, balances, signatures, host witnesses, persistent nonce changes or production publication is established.",
            "Finite Boolean execution does not cover arbitrary algebra-valued sbf behavior or universal compiler/runtime refinement.",
            "The equivalence proof manually translates pinned predicates and trusts Z3; execution and performance are separate claims.",
            "Report replacement assumes a caller-owned path with one writer; initial invalidation failure reports possible preexisting output and never starts qualification.",
        ],
    }
    output_path = ROOT / "tests/evidence/test_hygiene" / (EVIDENCE_ID + ".json")
    output_path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="ascii")
    print(output_path.relative_to(ROOT))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
