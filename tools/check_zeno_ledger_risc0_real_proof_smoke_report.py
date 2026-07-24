#!/usr/bin/env python3
"""Validate archived Risc0 real-proof smoke reports."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_v0 import (  # noqa: E402
    proof_metadata_hash_v0,
    validate_header_body_roots_v0,
    validate_proof_metadata_header_binding_v0,
)
from tools.zeno_ledger_risc0_proof_metadata import (  # noqa: E402
    build_header_derived_risc0_proof_metadata_diagnostic_v0,
)

REPORT_SCHEMA = "zenodex.risc0_real_proof_smoke.v0"
CHECK_REPORT_SCHEMA = "zenodex.risc0_real_proof_smoke_report_check.v0"
LEDGER_BINDING_SCHEMA = "zenodex.risc0_real_proof_smoke.ledger_binding.v0"
PROOF_TYPE = "risc0.zenodex_spot_transition.v1"
EXPECTED_HEADER_DERIVED_FIELDS = [
    "chain_id",
    "height",
    "pre_state_root",
    "post_state_root",
    "tx_root",
    "evidence_root",
    "body_root",
]
DEFAULT_REQUIRED_CASES = frozenset(
    {
        "empty",
        "faucet_mint",
        "create_pool",
        "swap_exact_in",
        "add_liquidity",
        "remove_liquidity",
        "spot_block_liquidity_cycle",
    }
)


def validate_risc0_real_proof_smoke_report_v0(
    report: Any,
    *,
    required_cases: set[str] | frozenset[str] = DEFAULT_REQUIRED_CASES,
    require_proof_files: bool = False,
) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(report, "report", errors)
    if obj.get("schema") != REPORT_SCHEMA:
        errors.append("schema mismatch")
    if obj.get("ok") is not True:
        errors.append("ok must be true")

    cases = _list(obj.get("cases"), "cases", errors)
    case_count = _nonnegative_int(obj.get("case_count"), "case_count", errors)
    if case_count is not None and case_count != len(cases):
        errors.append("case_count must match cases length")

    seen_cases: set[str] = set()
    case_reports: list[dict[str, Any]] = []
    for index, raw_case in enumerate(cases):
        item_errors: list[str] = []
        item = _mapping(raw_case, f"cases[{index}]", item_errors)
        case_name = _str(item.get("case"), f"cases[{index}].case", item_errors)
        proof_type = _str(item.get("proof_type"), f"cases[{index}].proof_type", item_errors)
        _hex32(item.get("state_hash"), f"cases[{index}].state_hash", item_errors)
        _hex32(item.get("post_app_hash"), f"cases[{index}].post_app_hash", item_errors)
        _hex32(item.get("txs_commitment"), f"cases[{index}].txs_commitment", item_errors)
        image_id = _str(item.get("risc0_image_id"), f"cases[{index}].risc0_image_id", item_errors)
        if image_id is not None and not _is_hex(image_id, 64):
            item_errors.append(f"cases[{index}].risc0_image_id must be 64-char hex")
        proof_base64_len = _positive_int(
            item.get("proof_base64_len"), f"cases[{index}].proof_base64_len", item_errors
        )
        proof_path = _str(item.get("proof_path"), f"cases[{index}].proof_path", item_errors)
        binding = _mapping(item.get("ledger_binding"), f"cases[{index}].ledger_binding", item_errors)
        if binding:
            if binding.get("schema") != LEDGER_BINDING_SCHEMA:
                item_errors.append(f"cases[{index}].ledger_binding.schema mismatch")
            if binding.get("status") != "non_authoritative_header_derived_metadata":
                item_errors.append(f"cases[{index}].ledger_binding.status mismatch")
            if binding.get("authority_scope") != "none":
                item_errors.append(f"cases[{index}].ledger_binding.authority_scope mismatch")
            if binding.get("header_derived_fields") != EXPECTED_HEADER_DERIVED_FIELDS:
                item_errors.append(f"cases[{index}].ledger_binding.header_derived_fields mismatch")
            for key in (
                "proof_authority_satisfied",
                "settlement_authority",
                "production_authority",
            ):
                if binding.get(key) is not False:
                    item_errors.append(f"cases[{index}].ledger_binding.{key} must be false")
            for key in (
                "ok",
                "header_bound",
                "body_checked",
                "post_state_root_checked",
                "pre_state_root_checked",
            ):
                _true(binding.get(key), f"cases[{index}].ledger_binding.{key}", item_errors)
            _nonnegative_int(
                binding.get("body_tx_count"),
                f"cases[{index}].ledger_binding.body_tx_count",
                item_errors,
            )
            for key in (
                "body_path",
                "header_path",
                "metadata_path",
            ):
                path_value = _str(binding.get(key), f"cases[{index}].ledger_binding.{key}", item_errors)
                if require_proof_files and path_value is not None:
                    path = Path(path_value)
                    if not path.is_file():
                        item_errors.append(f"cases[{index}].ledger_binding.{key} does not exist")
                    elif path.stat().st_size == 0:
                        item_errors.append(f"cases[{index}].ledger_binding.{key} must be non-empty")
            for key in (
                "proof_journal_hash",
                "pre_state_root",
                "post_state_root",
                "tx_root",
                "body_root",
                "evidence_root",
                "ledger_app_hash",
            ):
                _hex32(binding.get(key), f"cases[{index}].ledger_binding.{key}", item_errors)
        if proof_type is not None and proof_type != PROOF_TYPE:
            item_errors.append(f"cases[{index}].proof_type mismatch")
        if case_name is not None:
            if case_name in seen_cases:
                item_errors.append(f"cases[{index}].case must be unique")
            seen_cases.add(case_name)
            pre_app_hash = item.get("pre_app_hash")
            if case_name == "empty":
                if pre_app_hash != "":
                    item_errors.append("empty case pre_app_hash must be empty")
            elif not _is_hex(pre_app_hash, 64):
                item_errors.append(f"cases[{index}].pre_app_hash must be 64-char hex")
        if require_proof_files and proof_path is not None:
            path = Path(proof_path)
            if not path.is_file():
                item_errors.append(f"cases[{index}].proof_path does not exist")
            elif proof_base64_len is not None and path.stat().st_size == 0:
                item_errors.append(f"cases[{index}].proof_path must be non-empty")
        if require_proof_files and proof_path is not None and binding:
            _validate_artifact_binding(
                case_index=index,
                case=item,
                binding=binding,
                proof_path=Path(proof_path),
                errors=item_errors,
            )
        errors.extend(item_errors)
        case_reports.append(
            {
                "case": case_name,
                "ok": not item_errors,
                "ledger_binding_ok": bool(binding) and not item_errors,
                "errors": item_errors,
            }
        )

    missing_cases = sorted(set(required_cases) - seen_cases)
    unexpected_cases = sorted(seen_cases - set(required_cases))
    if missing_cases:
        errors.append(f"missing required cases: {','.join(missing_cases)}")
    if unexpected_cases:
        errors.append(f"unexpected cases: {','.join(unexpected_cases)}")

    return {
        "schema": CHECK_REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "required_cases": sorted(required_cases),
        "case_count": len(cases),
        "cases": case_reports,
    }


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if isinstance(value, Mapping):
        return value
    errors.append(f"{name} must be an object")
    return {}


def _list(value: Any, name: str, errors: list[str]) -> list[Any]:
    if isinstance(value, list):
        return value
    errors.append(f"{name} must be a list")
    return []


def _str(value: Any, name: str, errors: list[str]) -> str | None:
    if isinstance(value, str) and value:
        return value
    errors.append(f"{name} must be a non-empty string")
    return None


def _nonnegative_int(value: Any, name: str, errors: list[str]) -> int | None:
    if isinstance(value, int) and not isinstance(value, bool) and value >= 0:
        return value
    errors.append(f"{name} must be a non-negative int")
    return None


def _positive_int(value: Any, name: str, errors: list[str]) -> int | None:
    if isinstance(value, int) and not isinstance(value, bool) and value > 0:
        return value
    errors.append(f"{name} must be a positive int")
    return None


def _true(value: Any, name: str, errors: list[str]) -> None:
    if value is not True:
        errors.append(f"{name} must be true")


def _hex32(value: Any, name: str, errors: list[str]) -> None:
    if not _is_hex(value, 64):
        errors.append(f"{name} must be 64-char hex")


def _is_hex(value: Any, length: int) -> bool:
    if not isinstance(value, str):
        return False
    text = value[2:] if value.startswith("0x") else value
    return len(text) == length and all(ch in "0123456789abcdefABCDEF" for ch in text)


def _hex_text(value: Any) -> str | None:
    if not isinstance(value, str):
        return None
    text = value[2:] if value.startswith("0x") else value
    return text.lower()


def _hex_equal(actual: Any, expected: Any) -> bool:
    return _hex_text(actual) == _hex_text(expected)


def _expect_hex_equal(actual: Any, expected: Any, name: str, errors: list[str]) -> None:
    if not _hex_equal(actual, expected):
        errors.append(f"{name} mismatch")


def _load_json_mapping(path: Path, name: str, errors: list[str]) -> Mapping[str, Any] | None:
    try:
        value = _load_json(path)
    except Exception as exc:  # noqa: BLE001
        errors.append(f"{name} could not be loaded: {exc}")
        return None
    if not isinstance(value, Mapping):
        errors.append(f"{name} must be an object")
        return None
    return value


def _validate_artifact_binding(
    *,
    case_index: int,
    case: Mapping[str, Any],
    binding: Mapping[str, Any],
    proof_path: Path,
    errors: list[str],
) -> None:
    prefix = f"cases[{case_index}].artifact_binding"
    if not proof_path.is_file():
        return
    proof = _load_json_mapping(proof_path, f"{prefix}.proof", errors)
    body_path = binding.get("body_path")
    header_path = binding.get("header_path")
    metadata_path = binding.get("metadata_path")
    if not isinstance(body_path, str) or not isinstance(header_path, str) or not isinstance(metadata_path, str):
        return
    body = _load_json_mapping(Path(body_path), f"{prefix}.body", errors)
    header = _load_json_mapping(Path(header_path), f"{prefix}.header", errors)
    metadata = _load_json_mapping(Path(metadata_path), f"{prefix}.metadata", errors)
    if proof is None or body is None or header is None or metadata is None:
        return

    meta = proof.get("meta")
    if not isinstance(meta, Mapping):
        errors.append(f"{prefix}.proof.meta must be an object")
        return

    try:
        validate_header_body_roots_v0(dict(header), dict(body))
    except Exception as exc:  # noqa: BLE001
        errors.append(f"{prefix}.header_body_roots rejected: {exc}")

    try:
        validate_proof_metadata_header_binding_v0(dict(metadata), dict(header))
    except Exception as exc:  # noqa: BLE001
        errors.append(f"{prefix}.proof_metadata_header_binding rejected: {exc}")

    try:
        rebuilt = build_header_derived_risc0_proof_metadata_diagnostic_v0(
            proof_envelope=proof,
            header=header,
            conflict_schedule_hash=str(metadata.get("conflict_schedule_hash")),
            feature_suite_hash=str(metadata.get("feature_suite_hash")),
            dependency_lock_hash=str(metadata.get("dependency_lock_hash")),
            toolchain_lock_hash=str(metadata.get("toolchain_lock_hash")),
        )
        if rebuilt != dict(metadata):
            errors.append(f"{prefix}.metadata does not match proof/header rebuild")
    except Exception as exc:  # noqa: BLE001
        errors.append(f"{prefix}.metadata rebuild rejected: {exc}")

    proof_journal_hash: str | None = None
    try:
        proof_journal_hash = proof_metadata_hash_v0(dict(metadata))
    except Exception as exc:  # noqa: BLE001
        errors.append(f"{prefix}.metadata hash rejected: {exc}")

    _expect_hex_equal(case.get("state_hash"), proof.get("state_hash"), f"{prefix}.state_hash", errors)
    if case.get("proof_type") != proof.get("proof_type"):
        errors.append(f"{prefix}.proof_type mismatch")
    proof_b64 = proof.get("proof")
    if isinstance(proof_b64, str) and case.get("proof_base64_len") != len(proof_b64):
        errors.append(f"{prefix}.proof_base64_len mismatch")

    _expect_hex_equal(case.get("post_app_hash"), meta.get("post_app_hash"), f"{prefix}.post_app_hash", errors)
    if case.get("pre_app_hash") != meta.get("pre_app_hash"):
        errors.append(f"{prefix}.pre_app_hash mismatch")
    _expect_hex_equal(case.get("txs_commitment"), meta.get("txs_commitment"), f"{prefix}.txs_commitment", errors)
    _expect_hex_equal(case.get("risc0_image_id"), meta.get("risc0_image_id"), f"{prefix}.risc0_image_id", errors)

    transactions = body.get("transactions")
    if isinstance(transactions, list) and binding.get("body_tx_count") != len(transactions):
        errors.append(f"{prefix}.body_tx_count mismatch")

    if proof_journal_hash is not None:
        _expect_hex_equal(binding.get("proof_journal_hash"), proof_journal_hash, f"{prefix}.proof_journal_hash", errors)
        _expect_hex_equal(header.get("proof_journal_hash"), proof_journal_hash, f"{prefix}.header_proof_journal_hash", errors)
    _expect_hex_equal(binding.get("pre_state_root"), header.get("pre_state_root"), f"{prefix}.pre_state_root", errors)
    _expect_hex_equal(binding.get("post_state_root"), header.get("post_state_root"), f"{prefix}.post_state_root", errors)
    _expect_hex_equal(binding.get("tx_root"), header.get("tx_root"), f"{prefix}.tx_root", errors)
    _expect_hex_equal(binding.get("body_root"), header.get("body_root"), f"{prefix}.body_root", errors)
    _expect_hex_equal(binding.get("evidence_root"), header.get("evidence_root"), f"{prefix}.evidence_root", errors)
    _expect_hex_equal(binding.get("ledger_app_hash"), header.get("app_hash"), f"{prefix}.ledger_app_hash", errors)
    _expect_hex_equal(meta.get("post_app_hash"), header.get("post_state_root"), f"{prefix}.post_state_root_checked", errors)
    if meta.get("pre_app_hash") != "":
        _expect_hex_equal(meta.get("pre_app_hash"), header.get("pre_state_root"), f"{prefix}.pre_state_root_checked", errors)


def _load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("report", type=Path)
    parser.add_argument("--require-proof-files", action="store_true")
    parser.add_argument(
        "--required-case",
        action="append",
        choices=sorted(DEFAULT_REQUIRED_CASES),
        help="Required case name. May be supplied more than once. Defaults to the full supported set.",
    )
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    check = validate_risc0_real_proof_smoke_report_v0(
        _load_json(args.report),
        required_cases=DEFAULT_REQUIRED_CASES if args.required_case is None else set(args.required_case),
        require_proof_files=bool(args.require_proof_files),
    )
    print(json.dumps(check, sort_keys=True, indent=2 if args.pretty else None))
    return 0 if check["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
