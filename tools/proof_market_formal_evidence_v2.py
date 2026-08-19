"""Load source-pinned formal evidence for the proof-market V2 packet."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any, Final

REPO_ROOT: Final = Path(__file__).resolve().parents[1]


def _sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"{relative_path} must contain a JSON object")
    return value


def _pin_matches(relative_path: str, expected_sha256: str) -> bool:
    return _sha256((REPO_ROOT / relative_path).read_bytes()) == expected_sha256


def _fault_race_evidence(counterexamples: list[dict[str, Any]]) -> dict[str, bool]:
    fault_race = next(
        row
        for row in counterexamples
        if row["id"] == "PROVER_FAULT_WITNESS_VERIFICATION_RACE"
    )
    mutant_path = str(fault_race["mutant_path"])
    report_path = str(fault_race["mutant_verification_report_path"])
    bundle_path = str(fault_race["mutant_bundle_result_path"])
    report = _load_json(report_path)
    bundle = _load_json(bundle_path)
    verify_result = bundle["results"]["inductive_verify_submitted_work"]
    return {
        "fault_race_mutant_pins_match": all(
            (
                _pin_matches(mutant_path, fault_race["mutant_sha256"]),
                _pin_matches(
                    report_path,
                    fault_race["mutant_verification_report_sha256"],
                ),
                _pin_matches(
                    bundle_path,
                    fault_race["mutant_bundle_result_sha256"],
                ),
            )
        ),
        "fault_race_mutant_replays_sat": (
            report["verdict"] == "FAILED"
            and report["solvers_agreed"] is True
            and report["failed_queries"] == 1
            and verify_result["agreed"] is True
            and verify_result["final_result"] == "sat"
            and verify_result["z3_result"]["result"] == "sat"
            and verify_result["cvc5_result"]["result"] == "sat"
        ),
    }


def _esso_evidence() -> dict[str, Any]:
    receipt_path = "docs/research/PROOF_MARKET_PROCUREMENT_ESSO_V2.json"
    receipt = _load_json(receipt_path)
    replay = receipt["replay"]
    report_path = str(replay["verification_report_path"])
    bundle_path = str(replay["raw_bundle_result_path"])
    report = _load_json(report_path)
    bundle = _load_json(bundle_path)
    counterexamples = receipt["counterexamples"]
    evidence = {
        "receipt_path": receipt_path,
        "receipt_sha256": _sha256((REPO_ROOT / receipt_path).read_bytes()),
        "status": receipt["status"],
        "result": receipt["result"],
        "model_pin_matches": _pin_matches(
            str(receipt["model"]["path"]),
            receipt["model"]["sha256"],
        ),
        "verification_report_pin_matches": _pin_matches(
            report_path,
            replay["verification_report_sha256"],
        ),
        "raw_bundle_result_pin_matches": _pin_matches(
            bundle_path,
            replay["raw_bundle_result_sha256"],
        ),
        "preserved_report_replays_verified": (
            report["verdict"] == "VERIFIED"
            and report["solvers_agreed"] is True
            and report["passed_queries"] == 14
            and report["failed_queries"] == 0
            and all(
                result["final_result"] == "unsat"
                for result in bundle["results"].values()
            )
        ),
        "counterexample_ids": [row["id"] for row in counterexamples],
        "counterexample_retention": {
            row["id"]: row["evidence_retention"] for row in counterexamples
        },
        "toolchain": receipt["toolchain"],
    }
    evidence.update(_fault_race_evidence(counterexamples))
    return evidence


def _lean_evidence() -> dict[str, Any]:
    receipt_path = "docs/research/PROOF_MARKET_GAME_THEORY_LEAN_V2.json"
    receipt = _load_json(receipt_path)
    source = receipt["source"]
    replay = receipt["replay"]
    return {
        "receipt_path": receipt_path,
        "receipt_sha256": _sha256((REPO_ROOT / receipt_path).read_bytes()),
        "status": receipt["status"],
        "exit_code": replay["exit_code"],
        "stdout_sha256": replay["stdout_sha256"],
        "stderr_sha256": replay["stderr_sha256"],
        "toolchain": receipt["toolchain"],
        "compiled_theorems": receipt["compiled_theorems"],
        "placeholder_hits": replay["placeholder_hits"],
        "source_pin_matches": _pin_matches(
            str(source["path"]),
            source["sha256"],
        ),
        "root_import_pin_matches": _pin_matches(
            str(source["root_import_path"]),
            source["root_import_sha256"],
        ),
    }


def build_formal_evidence() -> dict[str, Any]:
    """Return the bounded ESSO and Lean observations with exact pin checks."""

    return {"esso": _esso_evidence(), "lean": _lean_evidence()}
