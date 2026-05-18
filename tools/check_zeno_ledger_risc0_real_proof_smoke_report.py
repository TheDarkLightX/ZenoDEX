#!/usr/bin/env python3
"""Validate archived Risc0 real-proof smoke reports."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

REPORT_SCHEMA = "zenodex.risc0_real_proof_smoke.v0"
CHECK_REPORT_SCHEMA = "zenodex.risc0_real_proof_smoke_report_check.v0"
PROOF_TYPE = "risc0.zenodex_spot_transition.v1"
DEFAULT_REQUIRED_CASES = frozenset({"empty", "faucet_mint", "create_pool", "swap_exact_in"})


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
        errors.extend(item_errors)
        case_reports.append({"case": case_name, "ok": not item_errors, "errors": item_errors})

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


def _hex32(value: Any, name: str, errors: list[str]) -> None:
    if not _is_hex(value, 64):
        errors.append(f"{name} must be 64-char hex")


def _is_hex(value: Any, length: int) -> bool:
    if not isinstance(value, str):
        return False
    text = value[2:] if value.startswith("0x") else value
    return len(text) == length and all(ch in "0123456789abcdefABCDEF" for ch in text)


def _load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("report", type=Path)
    parser.add_argument("--require-proof-files", action="store_true")
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    check = validate_risc0_real_proof_smoke_report_v0(
        _load_json(args.report),
        require_proof_files=bool(args.require_proof_files),
    )
    print(json.dumps(check, sort_keys=True, indent=2 if args.pretty else None))
    return 0 if check["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
