#!/usr/bin/env python3
"""Build/check the nonces (batch-sequencing) formal-spec contract.

Unlike cpmm/balances (Option A, where bounded spec-languages cannot express the surface), the nonce
batch-sequencing property is LINEAR over u32 and IS expressible in a bounded spec language: the
normative formal spec is the genuine machine-checked inductive ESSO model
`src/kernels/dex/nonce_batch_sequencing_v1.yaml` (verify-multi z3+cvc5 VERIFIED, Inductive(k=1), full
u32; inv_contiguous last_nonce==accepted_count is load-bearing, not effect-only) PLUS the Lean
batch-wrapper proof `ZenoDEXNonceBatchWrapper.lean` (decision-implies-safety: from the COMPUTED accept
predicate it DERIVES the exact successor range — not the tautology-adjacent ZenoDEXNonces.lean that
hypothesizes the range).

This contract pins those two artifacts and requires their committed receipts to attest them green:
the ESSO via the spot-proof receipt (id nonce_batch_sequencing_v1) and the Lean via the
kernel-assurance receipt (id nonce_batch_wrapper_lean, BUILT_NO_SORRY). It is the formal_spec
column's evidence; the proof_artifact (no-sorry build + live binding) and runtime/differential columns
remain separate.
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

import tools.check_kernel_assurance_public_receipt as kernel_assurance  # noqa: E402
import tools.spot_proof_public_receipt as spot_receipt  # noqa: E402

DEFAULT_CONTRACT = ROOT / "docs" / "assurance" / "nonce_batch_formal_spec_contract.json"
CONTRACT_SCHEMA = "zenodex.nonces.formal_spec_contract.v1"
CHECK_SCHEMA = "zenodex.nonces.formal_spec_contract_check.v1"

EXPECTED_CLAIM = (
    "The inductive ESSO model nonce_batch_sequencing_v1.yaml (verify-multi z3+cvc5 VERIFIED, "
    "Inductive(k=1), full u32) and the Lean batch-wrapper decision-implies-safety proof "
    "ZenoDEXNonceBatchWrapper.lean are the normative formal spec for the per-sender strict-sequential "
    "nonce batch-sequencing surface."
)
EXPECTED_SPEC_LANGUAGE = "ESSO inductive state machine (z3+cvc5) + Lean 4 theorem statements"
EXPECTED_GRADE = "A-"
EXPECTED_GRADE_REASON = (
    "The ESSO model is a genuine machine-checked inductive safety spec (load-bearing inv_contiguous; "
    "non-tautological accept guard n==last+1; both solvers agree over full u32), and the Lean wrapper "
    "derives the exact successor range from the computed accept predicate. Bounded spec-languages "
    "express this surface (linear over u32), so unlike cpmm/balances this is a direct spec, not Option A. "
    "no-sorry build and live binding stay under proof_artifact; reject/domain coverage under "
    "differential/runtime."
)
EXPECTED_PRODUCTION_MATRIX_EFFECT = (
    "Clears nonces.formal_spec; nonces.open_gaps_closed may clear if the other nonces columns are "
    "already true."
)
EXPECTED_ESSO_SPOT_PROOF_IDS = ["nonce_batch_sequencing_v1"]
EXPECTED_LEAN_KERNEL_PROOF_IDS = ["nonce_batch_wrapper_lean"]
EXPECTED_SOURCE_FILES = [
    "tools/check_nonce_batch_formal_spec_contract.py",
    "tests/test_check_nonce_batch_formal_spec_contract.py",
    "src/kernels/dex/nonce_batch_sequencing_v1.yaml",
    "lean-mathlib/Proofs/ZenoDEXNonceBatchWrapper.lean",
    ".github/workflows/runtime-shadow.yml",
    ".github/workflows/release-integrity.yml",
]
EXPECTED_WORKFLOW_TOKENS = [
    "tools/check_nonce_batch_formal_spec_contract.py check --pretty",
    "tests/test_check_nonce_batch_formal_spec_contract.py",
    "docs/assurance/nonce_batch_formal_spec_contract.json",
]
# The superseded single-step Tau guard is NOT the batch spec; flag if cited as the formal spec.
FORBIDDEN_SPEC_REFS = [
    "src/tau_specs/recommended/nonce_replay_guard_v1.tau",
    "src/tau_specs/nonce_replay_guard_v1.tau",
]
EXPECTED_FORMAL_ITEMS = [
    {
        "id": "esso_inductive_model",
        "path": "src/kernels/dex/nonce_batch_sequencing_v1.yaml",
        "tokens": [
            'model_id: "nonce_batch_sequencing_v1"',
            "inv_contiguous",
            "inv_monotone_step",
        ],
    },
    {
        "id": "lean_decision_implies_safety",
        "path": "lean-mathlib/Proofs/ZenoDEXNonceBatchWrapper.lean",
        "tokens": [
            "def acceptsSortedFold",
            "def successorRange",
            "def batchAccepts",
            "theorem batch_accept_decision_implies_safety",
            "theorem canonical_batch_accept_decision_implies_exact_ranges",
        ],
    },
]
ALLOWED_KEYS = {
    "schema",
    "surface_id",
    "matrix_column",
    "claim",
    "spec_language",
    "formal_items",
    "required_esso_spot_proof_ids",
    "required_lean_kernel_assurance_proof_ids",
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
        "surface_id": "nonces",
        "matrix_column": "formal_spec",
        "claim": EXPECTED_CLAIM,
        "spec_language": EXPECTED_SPEC_LANGUAGE,
        "formal_items": EXPECTED_FORMAL_ITEMS,
        "required_esso_spot_proof_ids": EXPECTED_ESSO_SPOT_PROOF_IDS,
        "required_lean_kernel_assurance_proof_ids": EXPECTED_LEAN_KERNEL_PROOF_IDS,
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
                errors.append(f"{item['id']}: missing spec token {token!r}")


def _contract_body_outside_forbidden_list(contract: Mapping[str, Any]) -> str:
    body = dict(contract)
    body.pop("forbidden_spec_refs", None)
    return json.dumps(body, sort_keys=True)


def _check_esso_attestation(errors: list[str]) -> None:
    report = spot_receipt.check_receipt_file()
    if report.get("ok") is not True:
        errors.append(f"spot proof receipt failed: {report.get('errors')}")
        return
    receipt = _load_json_object(spot_receipt.DEFAULT_RECEIPT)
    ids = {p.get("id") for p in receipt.get("proofs", []) if isinstance(p, Mapping)}
    missing = sorted(set(EXPECTED_ESSO_SPOT_PROOF_IDS) - ids)
    if missing:
        errors.append(f"spot proof receipt missing ESSO proof ids: {missing}")


def _check_lean_attestation(errors: list[str]) -> None:
    report = kernel_assurance.check_receipt_file()
    if report.get("ok") is not True:
        errors.append(f"kernel assurance receipt failed: {report.get('errors')}")
        return
    receipt = _load_json_object(kernel_assurance.DEFAULT_RECEIPT)
    ids = {p.get("id") for p in receipt.get("lean_proofs", []) if isinstance(p, Mapping)}
    missing = sorted(set(EXPECTED_LEAN_KERNEL_PROOF_IDS) - ids)
    if missing:
        errors.append(f"kernel assurance receipt missing Lean proof ids: {missing}")


def _check_workflows(errors: list[str]) -> None:
    workflow_text = (ROOT / ".github" / "workflows" / "runtime-shadow.yml").read_text(encoding="utf-8")
    release_text = (ROOT / ".github" / "workflows" / "release-integrity.yml").read_text(encoding="utf-8")
    combined = workflow_text + "\n" + release_text
    for token in EXPECTED_WORKFLOW_TOKENS:
        if token not in combined:
            errors.append(f"workflow is missing nonce formal-spec gate token: {token}")


def check_contract(path: Path = DEFAULT_CONTRACT) -> dict[str, Any]:
    errors: list[str] = []
    try:
        contract = _load_json_object(path)
        errors.extend(_unexpected_keys(contract))
        _expect_equal(contract, "schema", CONTRACT_SCHEMA, errors)
        _expect_equal(contract, "surface_id", "nonces", errors)
        _expect_equal(contract, "matrix_column", "formal_spec", errors)
        _expect_equal(contract, "claim", EXPECTED_CLAIM, errors)
        _expect_equal(contract, "spec_language", EXPECTED_SPEC_LANGUAGE, errors)
        _expect_equal(contract, "required_esso_spot_proof_ids", EXPECTED_ESSO_SPOT_PROOF_IDS, errors)
        _expect_equal(contract, "required_lean_kernel_assurance_proof_ids", EXPECTED_LEAN_KERNEL_PROOF_IDS, errors)
        _expect_equal(contract, "forbidden_spec_refs", FORBIDDEN_SPEC_REFS, errors)
        _expect_equal(contract, "grade", EXPECTED_GRADE, errors)
        _expect_equal(contract, "grade_reason", EXPECTED_GRADE_REASON, errors)
        _expect_equal(contract, "production_matrix_effect", EXPECTED_PRODUCTION_MATRIX_EFFECT, errors)
        # REVIEW [B -> A-]: Claude copied the forbidden-ref guard from the
        # sibling checkers, but that expression was unreachable because every
        # forbidden ref necessarily appears in `forbidden_spec_refs`. Remove the
        # allowlist field before scanning, so a stale Tau/Tau-like single-step
        # ref cannot ride along in another reviewed field after constants drift.
        rendered = _contract_body_outside_forbidden_list(contract)
        for ref in FORBIDDEN_SPEC_REFS:
            if ref in rendered:
                errors.append(f"forbidden superseded spec ref appears outside forbidden list: {ref}")
        _check_source_hashes(contract, errors)
        _check_formal_items(contract, errors)
        _check_esso_attestation(errors)
        _check_lean_attestation(errors)
        _check_workflows(errors)
    except Exception as exc:  # noqa: BLE001 - evidence checkers fail closed
        errors.append(f"{type(exc).__name__}: {exc}")
    return {
        "schema": CHECK_SCHEMA,
        "ok": not errors,
        "contract": str(path),
        "errors": errors,
        "surface_id": "nonces",
        "matrix_column": "formal_spec",
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build/check the nonces batch-sequencing formal-spec contract.")
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
