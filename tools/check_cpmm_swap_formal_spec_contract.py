#!/usr/bin/env python3
"""Build/check the CPMM swap formal-spec contract.

This is the matrix decision that resolves the old ``cpmm_swap.formal_spec``
blocker for nonlinear u256 arithmetic: the formal spec for this surface is the
source-pinned Lean 4 contract made of definitions and theorem statements in the
CPMM proof modules.  The proof_artifact column remains separate: it records that
the same sources were built without sorry/unsafe and bound to the live kernel by
runtime tests.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import tools.spot_proof_public_receipt as spot_receipt  # noqa: E402

DEFAULT_CONTRACT = ROOT / "docs" / "assurance" / "cpmm_swap_formal_spec_contract.json"
CONTRACT_SCHEMA = "zenodex.cpmm_swap.formal_spec_contract.v1"
CHECK_SCHEMA = "zenodex.cpmm_swap.formal_spec_contract_check.v1"

EXPECTED_CLAIM = (
    "Lean 4 definitions and theorem statements are the normative formal spec for "
    "the cpmm_swap nonlinear u256 arithmetic surface."
)
EXPECTED_GRADE = "A"
EXPECTED_GRADE_REASON = (
    "Source-pinned Lean definitions specify exact-in output, exact-out gross input, "
    "fee rounding, and k monotonicity. This clears the formal_spec column because "
    "the spec lives in Lean for this nonlinear surface; proof/build and runtime "
    "bindings remain checked by the proof_artifact and differential/runtime columns."
)
EXPECTED_PRODUCTION_MATRIX_EFFECT = "Clears cpmm_swap.formal_spec; cpmm_swap.open_gaps_closed may clear if the other cpmm columns are already true."
EXPECTED_SPEC_LANGUAGE = "Lean 4 theorem statements and definitions"
EXPECTED_PROOF_IDS = [
    "cpmm_invariants_lean",
    "cpmm_v8_exact_in_admissibility_lean",
    "cpmm_v8_exact_out_minimality_lean",
]
EXPECTED_SOURCE_FILES = [
    "tools/check_cpmm_swap_formal_spec_contract.py",
    "tests/test_check_cpmm_swap_formal_spec_contract.py",
    "tools/spot_proof_public_manifest.json",
    "tools/spot_proof_public_receipt.py",
    "docs/assurance/spot_proof_public_receipt.json",
    "lean-mathlib/Proofs/CPMMInvariants.lean",
    "lean-mathlib/Proofs/CpmmSwapV8ExactInAdmissibility.lean",
    "lean-mathlib/Proofs/CpmmSwapV8ExactOutMinimality.lean",
    "tests/runtime/test_cpmm_v8_exact_in_lean_property_binding.py",
    "tests/runtime/test_cpmm_v8_exact_out_lean_property_binding.py",
    "tests/runtime/test_cpmm_v8_exact_out_k_conservation_binding.py",
    ".github/workflows/runtime-shadow.yml",
    ".github/workflows/release-integrity.yml",
]
EXPECTED_WORKFLOW_TOKENS = [
    "tools/check_cpmm_swap_formal_spec_contract.py check --pretty",
    "tests/test_check_cpmm_swap_formal_spec_contract.py",
    "docs/assurance/cpmm_swap_formal_spec_contract.json",
]
FORBIDDEN_SPEC_REFS = [
    "src/kernels/dex/cpmm_output_amount_v2.yaml",
    "src/kernels/dex/cpmm_output_amount_ref.yaml",
]
EXPECTED_FORMAL_ITEMS = [
    {
        "id": "exact_in_output_formula",
        "path": "lean-mathlib/Proofs/CpmmSwapV8ExactInAdmissibility.lean",
        "tokens": ["def exactInNet", "def exactInOutput", "theorem exactInAccepted_suffix"],
    },
    {
        "id": "exact_out_gross_minimality",
        "path": "lean-mathlib/Proofs/CpmmSwapV8ExactOutMinimality.lean",
        "tokens": [
            "def exactOutNetReq",
            "def exactOutGross",
            "def exactOutQuote",
            "theorem exactOutGross_sufficient_and_minimal",
        ],
    },
    {
        "id": "fee_and_k_monotonicity",
        "path": "lean-mathlib/Proofs/CPMMInvariants.lean",
        "tokens": [
            "def computeFee",
            "def netAmount",
            "def swapOutput",
            "theorem k_monotone_zero_fee",
            "theorem k_monotone_with_fee",
        ],
    },
]


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


def _unexpected_keys(obj: Mapping[str, Any], *, allowed: set[str], name: str) -> list[str]:
    extra = sorted(set(obj) - allowed)
    return [f"{name} has unexpected public field(s): {extra}"] if extra else []


def build_contract(path: Path) -> dict[str, Any]:
    contract = {
        "schema": CONTRACT_SCHEMA,
        "surface_id": "cpmm_swap",
        "matrix_column": "formal_spec",
        "claim": EXPECTED_CLAIM,
        "spec_language": EXPECTED_SPEC_LANGUAGE,
        "formal_items": EXPECTED_FORMAL_ITEMS,
        "required_spot_proof_ids": EXPECTED_PROOF_IDS,
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


def _check_spot_receipt(errors: list[str]) -> None:
    report = spot_receipt.check_receipt_file()
    if report.get("ok") is not True:
        errors.append(f"spot proof public receipt failed: {report.get('errors')}")
        return
    receipt = _load_json_object(spot_receipt.DEFAULT_RECEIPT)
    proof_ids = {proof.get("id") for proof in receipt.get("proofs", []) if isinstance(proof, Mapping)}
    missing = sorted(set(EXPECTED_PROOF_IDS) - proof_ids)
    if missing:
        errors.append(f"spot proof receipt missing CPMM proof ids: {missing}")


def _check_workflows(errors: list[str]) -> None:
    workflow_text = (ROOT / ".github" / "workflows" / "runtime-shadow.yml").read_text(encoding="utf-8")
    release_text = (ROOT / ".github" / "workflows" / "release-integrity.yml").read_text(encoding="utf-8")
    combined = workflow_text + "\n" + release_text
    for token in EXPECTED_WORKFLOW_TOKENS:
        if token not in combined:
            errors.append(f"workflow is missing CPMM formal-spec gate token: {token}")


def check_contract(path: Path = DEFAULT_CONTRACT) -> dict[str, Any]:
    errors: list[str] = []
    try:
        contract = _load_json_object(path)
        # REVIEW [B -> A-]: the contract pinned every load-bearing field, but
        # still accepted extra top-level keys. That is too wide for a green CBC
        # formal_spec artifact because a local path or unsupported claim label
        # could ride alongside the reviewed contract. The public envelope is now
        # exact.
        errors.extend(
            _unexpected_keys(
                contract,
                allowed={
                    "schema",
                    "surface_id",
                    "matrix_column",
                    "claim",
                    "spec_language",
                    "formal_items",
                    "required_spot_proof_ids",
                    "forbidden_spec_refs",
                    "source_hashes",
                    "grade",
                    "grade_reason",
                    "production_matrix_effect",
                },
                name="contract",
            )
        )
        _expect_equal(contract, "schema", CONTRACT_SCHEMA, errors)
        _expect_equal(contract, "surface_id", "cpmm_swap", errors)
        _expect_equal(contract, "matrix_column", "formal_spec", errors)
        _expect_equal(contract, "claim", EXPECTED_CLAIM, errors)
        _expect_equal(contract, "spec_language", EXPECTED_SPEC_LANGUAGE, errors)
        _expect_equal(contract, "required_spot_proof_ids", EXPECTED_PROOF_IDS, errors)
        _expect_equal(contract, "forbidden_spec_refs", FORBIDDEN_SPEC_REFS, errors)
        _expect_equal(contract, "grade", EXPECTED_GRADE, errors)
        _expect_equal(contract, "grade_reason", EXPECTED_GRADE_REASON, errors)
        _expect_equal(contract, "production_matrix_effect", EXPECTED_PRODUCTION_MATRIX_EFFECT, errors)
        rendered = json.dumps(contract, sort_keys=True)
        for ref in FORBIDDEN_SPEC_REFS:
            if ref in rendered and ref not in json.dumps(FORBIDDEN_SPEC_REFS):
                errors.append(f"forbidden placeholder spec ref appears outside forbidden list: {ref}")
        _check_source_hashes(contract, errors)
        _check_formal_items(contract, errors)
        _check_spot_receipt(errors)
        _check_workflows(errors)
    except Exception as exc:  # noqa: BLE001 - evidence checkers fail closed
        errors.append(f"{type(exc).__name__}: {exc}")
    return {
        "schema": CHECK_SCHEMA,
        "ok": not errors,
        "contract": str(path),
        "errors": errors,
        "surface_id": "cpmm_swap",
        "matrix_column": "formal_spec",
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build/check the CPMM swap formal-spec contract.")
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
