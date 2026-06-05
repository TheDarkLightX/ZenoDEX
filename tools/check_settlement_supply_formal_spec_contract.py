#!/usr/bin/env python3
"""Build/check the balances (settlement supply-conservation) formal-spec contract.

This is the owner-authorized Option-A matrix decision for the balances surface, mirroring the
cpmm_swap precedent: for a surface whose domain exceeds bounded spec-languages, the normative
formal spec IS the source-pinned Lean 4 contract (definitions + theorem statements).

Why Option A here (the principled justification, not laziness): the live settlement applies
`balance_deltas` / `reserve_deltas` that are `List[BalanceDelta]` of UNBOUNDED length (any number of
owners/pool-cells in a batch), and the supply-conservation property is a UNIVERSALLY-QUANTIFIED
statement over that variable-length multi-owner ledger (`supply_applyDeltas` is induction over a
`List Int` of arbitrary length). Tau (bv32) and ESSO model FINITE FIXED-ARITY bounded state machines:
a fixed-N instance is trivial linear arithmetic, but ∀-arity (any owner/cell count) is inexpressible.
So the bounded `balance_transition_v1.tau` / `balance_safety_v1.tau` limb contracts (single-cell,
32-bit) CANNOT formalize unbounded multi-owner batch conservation — citing them would be the
width-cast fake-green. They are listed in `forbidden_spec_refs`.

The proof_artifact column remains separate: it records that the same Lean sources are built without
sorry and bound to the live validate+apply path by the runtime binding test. This contract shares the
Lean file with proof_artifact (column collapse), exactly as owner-authorized for cpmm.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import tools.check_kernel_assurance_public_receipt as kernel_assurance  # noqa: E402

DEFAULT_CONTRACT = ROOT / "docs" / "assurance" / "settlement_supply_formal_spec_contract.json"
CONTRACT_SCHEMA = "zenodex.balances.formal_spec_contract.v1"
CHECK_SCHEMA = "zenodex.balances.formal_spec_contract_check.v1"

EXPECTED_CLAIM = (
    "Lean 4 definitions and theorem statements are the normative formal spec for the balances "
    "settlement supply-conservation surface, whose unbounded multi-owner batch arity (variable-length "
    "balance_deltas/reserve_deltas) exceeds bounded spec-languages (Tau bv32, ESSO finite-state)."
)
EXPECTED_SPEC_LANGUAGE = "Lean 4 theorem statements and definitions"
EXPECTED_GRADE = "A-"
EXPECTED_GRADE_REASON = (
    "Source-pinned Lean definitions (supply, applyDeltas, accepted) and theorems (supply_applyDeltas "
    "key lemma, accepted_preserves_supply headline, the contrapositive, two non-vacuity witnesses) "
    "specify the per-asset supply-conservation law over an unbounded-arity multi-owner ledger. This "
    "clears the formal_spec column because the spec lives in Lean for this unbounded surface; the "
    "no-sorry build and live validate+apply binding remain checked by the proof_artifact and "
    "runtime/differential columns."
)
EXPECTED_PRODUCTION_MATRIX_EFFECT = (
    "Clears balances.formal_spec; balances.open_gaps_closed may clear if the other balances columns "
    "are already true."
)
EXPECTED_KERNEL_PROOF_IDS = ["settlement_supply_conservation_lean"]
# Pin only files THIS contract owns. The kernel-assurance receipt/manifest/checker are validated
# DYNAMICALLY by _check_kernel_assurance (which re-runs check_receipt_file) rather than hash-pinned,
# so the concurrently-maintained kernel-assurance evidence does not drift this contract.
EXPECTED_SOURCE_FILES = [
    "tools/check_settlement_supply_formal_spec_contract.py",
    "tests/test_check_settlement_supply_formal_spec_contract.py",
    "lean-mathlib/Proofs/SettlementSupplyConservation.lean",
    "tests/runtime/test_settlement_supply_conservation_lean_binding.py",
    ".github/workflows/runtime-shadow.yml",
    ".github/workflows/release-integrity.yml",
]
EXPECTED_WORKFLOW_TOKENS = [
    "tools/check_settlement_supply_formal_spec_contract.py check --pretty",
    "tests/test_check_settlement_supply_formal_spec_contract.py",
    "docs/assurance/settlement_supply_formal_spec_contract.json",
]
FORBIDDEN_SPEC_REFS = [
    "src/tau_specs/balance_transition_v1.tau",
    "src/tau_specs/balance_safety_v1.tau",
    "src/tau_specs/recommended/balance_transition_v1.tau",
    "src/tau_specs/recommended/balance_safety_v1.tau",
]
EXPECTED_FORMAL_ITEMS = [
    {
        "id": "supply_and_apply_model",
        "path": "lean-mathlib/Proofs/SettlementSupplyConservation.lean",
        "tokens": ["def supply", "def applyDeltas", "def accepted"],
    },
    {
        "id": "supply_conservation_theorems",
        "path": "lean-mathlib/Proofs/SettlementSupplyConservation.lean",
        "tokens": [
            "theorem supply_applyDeltas",
            "theorem accepted_preserves_supply",
            "theorem supply_changed_implies_not_accepted",
        ],
    },
    {
        "id": "nonvacuity_witnesses",
        "path": "lean-mathlib/Proofs/SettlementSupplyConservation.lean",
        "tokens": [
            "theorem witness_accepted_preserves_noncanceling",
            "theorem witness_unbalanced_creates_supply",
        ],
    },
]
# The `accepted` predicate MUST be the Σdelta=0 gate used as a hypothesis — never a smuggled
# supply-equality (the forbidden tautology, cf. SettlementConservationLive.lean).
REQUIRED_NONTAUTOLOGY_TOKEN = "supply balDeltas + supply resDeltas = 0"
REQUIRED_ACCEPTED_DEFINITION_RE = re.compile(
    r"def\s+accepted\s+\(balDeltas\s+resDeltas\s+:\s+Ledger\)\s+:\s+Prop\s*:=\s*"
    r"supply\s+balDeltas\s+\+\s+supply\s+resDeltas\s+=\s+0",
    re.MULTILINE,
)
ALLOWED_KEYS = {
    "schema",
    "surface_id",
    "matrix_column",
    "claim",
    "spec_language",
    "formal_items",
    "required_kernel_assurance_proof_ids",
    "forbidden_spec_refs",
    "source_hashes",
    "grade",
    "grade_reason",
    "production_matrix_effect",
}


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _source_hashes() -> dict[str, str]:
    return {rel: _sha256_file(ROOT / rel) for rel in EXPECTED_SOURCE_FILES}


def _load_json_object(path: Path) -> dict[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, dict):
        raise ValueError(f"{path}: top-level JSON value must be an object")
    return obj


def _unexpected_keys(obj: Mapping[str, Any]) -> list[str]:
    extra = sorted(set(obj) - ALLOWED_KEYS)
    return [f"contract has unexpected public field(s): {extra}"] if extra else []


def build_contract(path: Path) -> dict[str, Any]:
    contract = {
        "schema": CONTRACT_SCHEMA,
        "surface_id": "balances",
        "matrix_column": "formal_spec",
        "claim": EXPECTED_CLAIM,
        "spec_language": EXPECTED_SPEC_LANGUAGE,
        "formal_items": EXPECTED_FORMAL_ITEMS,
        "required_kernel_assurance_proof_ids": EXPECTED_KERNEL_PROOF_IDS,
        "forbidden_spec_refs": FORBIDDEN_SPEC_REFS,
        "source_hashes": _source_hashes(),
        "grade": EXPECTED_GRADE,
        "grade_reason": EXPECTED_GRADE_REASON,
        "production_matrix_effect": EXPECTED_PRODUCTION_MATRIX_EFFECT,
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(contract, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return contract


def _expect_equal(contract: Mapping[str, Any], field: str, expected: Any, errors: list[str]) -> None:
    if contract.get(field) != expected:
        errors.append(f"{field} mismatch")


def _check_source_hashes(contract: Mapping[str, Any], errors: list[str]) -> None:
    raw = contract.get("source_hashes")
    if not isinstance(raw, Mapping):
        errors.append("source_hashes must be an object")
        return
    if sorted(raw) != sorted(EXPECTED_SOURCE_FILES):
        errors.append("source hash file set mismatch")
    for rel, pinned in raw.items():
        if not isinstance(rel, str) or not isinstance(pinned, str):
            errors.append("source_hashes entries must map string paths to string sha256 values")
            continue
        try:
            actual = _sha256_file(ROOT / rel)
        except OSError as exc:
            errors.append(f"source file unreadable: {rel}: {exc}")
            continue
        if actual != pinned:
            errors.append(f"source hash mismatch: {rel}")


def _check_formal_items(contract: Mapping[str, Any], errors: list[str]) -> None:
    if contract.get("formal_items") != EXPECTED_FORMAL_ITEMS:
        errors.append("formal_items mismatch")
        return
    for item in EXPECTED_FORMAL_ITEMS:
        text = (ROOT / item["path"]).read_text(encoding="utf-8")
        for token in item["tokens"]:
            if token not in text:
                errors.append(f"{item['id']}: missing Lean declaration token {token!r}")


def _check_nontautology(errors: list[str]) -> None:
    """The spec must keep the Σdelta=0 GATE as the `accepted` hypothesis (not a smuggled
    supply-equality). Guards against silently editing the spec into the forbidden tautology."""
    lean = (ROOT / "lean-mathlib" / "Proofs" / "SettlementSupplyConservation.lean").read_text(
        encoding="utf-8"
    )
    # REVIEW [B -> A-]: a bare token search could be satisfied by a comment
    # after a weakened `accepted` definition. Require the actual Lean definition
    # to be the validator's Σdelta=0 gate.
    if REQUIRED_NONTAUTOLOGY_TOKEN not in lean or not REQUIRED_ACCEPTED_DEFINITION_RE.search(lean):
        errors.append(
            "formal spec lost its Σdelta=0 gate hypothesis (accepted := "
            f"{REQUIRED_NONTAUTOLOGY_TOKEN!r}); refusing to certify a possibly-tautological spec"
        )
    if "sorry" in lean or "admit" in lean:
        errors.append("formal spec Lean source is not sorry-free")


def _check_kernel_assurance(errors: list[str]) -> None:
    """The Lean spec must be a green, no-sorry, source-pinned kernel-assurance proof."""
    report = kernel_assurance.check_receipt_file()
    if report.get("ok") is not True:
        errors.append(f"kernel assurance receipt failed: {report.get('errors')}")
        return
    receipt = _load_json_object(kernel_assurance.DEFAULT_RECEIPT)
    proof_ids = {p.get("id") for p in receipt.get("lean_proofs", []) if isinstance(p, Mapping)}
    missing = sorted(set(EXPECTED_KERNEL_PROOF_IDS) - proof_ids)
    if missing:
        errors.append(f"kernel assurance receipt missing required Lean proof ids: {missing}")


def _check_workflows(errors: list[str]) -> None:
    workflow_text = (ROOT / ".github" / "workflows" / "runtime-shadow.yml").read_text(encoding="utf-8")
    release_text = (ROOT / ".github" / "workflows" / "release-integrity.yml").read_text(encoding="utf-8")
    combined = workflow_text + "\n" + release_text
    for token in EXPECTED_WORKFLOW_TOKENS:
        if token not in combined:
            errors.append(f"workflow is missing settlement-supply formal-spec gate token: {token}")


def check_contract(path: Path = DEFAULT_CONTRACT) -> dict[str, Any]:
    errors: list[str] = []
    try:
        contract = _load_json_object(path)
        errors.extend(_unexpected_keys(contract))
        _expect_equal(contract, "schema", CONTRACT_SCHEMA, errors)
        _expect_equal(contract, "surface_id", "balances", errors)
        _expect_equal(contract, "matrix_column", "formal_spec", errors)
        _expect_equal(contract, "claim", EXPECTED_CLAIM, errors)
        _expect_equal(contract, "spec_language", EXPECTED_SPEC_LANGUAGE, errors)
        _expect_equal(contract, "required_kernel_assurance_proof_ids", EXPECTED_KERNEL_PROOF_IDS, errors)
        _expect_equal(contract, "forbidden_spec_refs", FORBIDDEN_SPEC_REFS, errors)
        _expect_equal(contract, "grade", EXPECTED_GRADE, errors)
        _expect_equal(contract, "grade_reason", EXPECTED_GRADE_REASON, errors)
        _expect_equal(contract, "production_matrix_effect", EXPECTED_PRODUCTION_MATRIX_EFFECT, errors)
        rendered = json.dumps(contract, sort_keys=True)
        for ref in FORBIDDEN_SPEC_REFS:
            if ref in rendered and ref not in json.dumps(FORBIDDEN_SPEC_REFS):
                errors.append(f"forbidden bounded spec ref appears outside forbidden list: {ref}")
        _check_source_hashes(contract, errors)
        _check_formal_items(contract, errors)
        _check_nontautology(errors)
        _check_kernel_assurance(errors)
        _check_workflows(errors)
    except Exception as exc:  # noqa: BLE001 - evidence checkers fail closed
        errors.append(f"{type(exc).__name__}: {exc}")
    return {
        "schema": CHECK_SCHEMA,
        "ok": not errors,
        "contract": str(path),
        "errors": errors,
        "surface_id": "balances",
        "matrix_column": "formal_spec",
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Build/check the balances settlement supply-conservation formal-spec contract."
    )
    sub = parser.add_subparsers(dest="cmd", required=True)
    p_build = sub.add_parser("build")
    p_build.add_argument("--contract", type=Path, default=DEFAULT_CONTRACT)
    p_build.add_argument("--pretty", action="store_true")
    p_check = sub.add_parser("check")
    p_check.add_argument("--contract", type=Path, default=DEFAULT_CONTRACT)
    p_check.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    if args.cmd == "build":
        result = build_contract(args.contract)
        ok = True
    else:
        result = check_contract(args.contract)
        ok = bool(result.get("ok"))
    print(json.dumps(result, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
