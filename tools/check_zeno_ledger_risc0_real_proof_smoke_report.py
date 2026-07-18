#!/usr/bin/env python3
"""Validate archived Risc0 real-proof smoke reports."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.risc0_route_body_projection import (  # noqa: E402
    project_route_body_transactions_to_proof_v1,
    route_body_projection_contract_hash_v1,
    route_body_projection_contract_v1,
)
from src.integration.zeno_ledger_v0 import (  # noqa: E402
    hash_v0,
    proof_metadata_hash_v0,
    validate_header_body_roots_v0,
    validate_proof_metadata_header_binding_v0,
)
from tools.zeno_ledger_risc0_proof_metadata import build_risc0_proof_metadata_v0  # noqa: E402

REPORT_SCHEMA = "zenodex.risc0_real_proof_smoke.v0"
CHECK_REPORT_SCHEMA = "zenodex.risc0_real_proof_smoke_report_check.v0"
LEDGER_BINDING_SCHEMA = "zenodex.risc0_real_proof_smoke.ledger_binding.v0"
PROOF_TYPE = "risc0.zenodex_spot_transition.v1"
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
ROUTE_ORDER_RECEIPT_REQUIRED_CASES = frozenset({"route_order"})
ALLOWED_REQUIRED_CASES = DEFAULT_REQUIRED_CASES | ROUTE_ORDER_RECEIPT_REQUIRED_CASES


def validate_risc0_real_proof_smoke_report_v0(
    report: Any,
    *,
    required_cases: set[str] | frozenset[str] = DEFAULT_REQUIRED_CASES,
    require_proof_files: bool = False,
    base_dir: Path | None = None,
    risc0_cli_bin: Path | None = None,
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
            _nonnegative_int(
                binding.get("proof_tx_count"),
                f"cases[{index}].ledger_binding.proof_tx_count",
                item_errors,
            )
            for key in (
                "body_path",
                "header_path",
                "metadata_path",
                "proof_transactions_path",
            ):
                path_value = _str(binding.get(key), f"cases[{index}].ledger_binding.{key}", item_errors)
                if require_proof_files and path_value is not None:
                    path = _resolve_path(path_value, base_dir=base_dir)
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
                "body_transactions_hash",
                "proof_transactions_hash",
            ):
                _hex32(binding.get(key), f"cases[{index}].ledger_binding.{key}", item_errors)
            _bool(
                binding.get("proof_transactions_match_body"),
                f"cases[{index}].ledger_binding.proof_transactions_match_body",
                item_errors,
            )
            _true(
                binding.get("body_to_proof_projection_checked"),
                f"cases[{index}].ledger_binding.body_to_proof_projection_checked",
                item_errors,
            )
            _validate_projection_contract_binding(
                binding,
                prefix=f"cases[{index}].ledger_binding",
                errors=item_errors,
            )
            if case_name in ROUTE_ORDER_RECEIPT_REQUIRED_CASES:
                _true(
                    binding.get("body_tx_execution_order_commitment_checked"),
                    f"cases[{index}].ledger_binding.body_tx_execution_order_commitment_checked",
                    item_errors,
                )
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
            path = _resolve_path(proof_path, base_dir=base_dir)
            if not path.is_file():
                item_errors.append(f"cases[{index}].proof_path does not exist")
            elif proof_base64_len is not None and path.stat().st_size == 0:
                item_errors.append(f"cases[{index}].proof_path must be non-empty")
        if require_proof_files and proof_path is not None and binding:
            _validate_artifact_binding(
                case_index=index,
                case=item,
                binding=binding,
                proof_path=_resolve_path(proof_path, base_dir=base_dir),
                base_dir=base_dir,
                risc0_cli_bin=risc0_cli_bin,
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


def _bool(value: Any, name: str, errors: list[str]) -> None:
    if not isinstance(value, bool):
        errors.append(f"{name} must be a bool")


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


def _validate_projection_contract_binding(
    binding: Mapping[str, Any],
    *,
    prefix: str,
    errors: list[str],
) -> None:
    expected_contract = route_body_projection_contract_v1()
    contract = _mapping(binding.get("projection_contract"), f"{prefix}.projection_contract", errors)
    if contract and dict(contract) != expected_contract:
        errors.append(f"{prefix}.projection_contract mismatch")
    _hex32(binding.get("projection_contract_hash"), f"{prefix}.projection_contract_hash", errors)
    _expect_hex_equal(
        binding.get("projection_contract_hash"),
        route_body_projection_contract_hash_v1(),
        f"{prefix}.projection_contract_hash",
        errors,
    )


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


def _load_json_list(path: Path, name: str, errors: list[str]) -> list[Any] | None:
    try:
        value = _load_json(path)
    except Exception as exc:  # noqa: BLE001
        errors.append(f"{name} could not be loaded: {exc}")
        return None
    if not isinstance(value, list):
        errors.append(f"{name} must be a list")
        return None
    return value


def _resolve_path(path: str, *, base_dir: Path | None) -> Path:
    raw = Path(path)
    if raw.is_absolute() or base_dir is None:
        return raw
    return base_dir / raw


def _validate_artifact_binding(
    *,
    case_index: int,
    case: Mapping[str, Any],
    binding: Mapping[str, Any],
    proof_path: Path,
    base_dir: Path | None,
    risc0_cli_bin: Path | None,
    errors: list[str],
) -> None:
    prefix = f"cases[{case_index}].artifact_binding"
    if not proof_path.is_file():
        return
    proof = _load_json_mapping(proof_path, f"{prefix}.proof", errors)
    body_path = binding.get("body_path")
    header_path = binding.get("header_path")
    metadata_path = binding.get("metadata_path")
    proof_transactions_path = binding.get("proof_transactions_path")
    if (
        not isinstance(body_path, str)
        or not isinstance(header_path, str)
        or not isinstance(metadata_path, str)
        or not isinstance(proof_transactions_path, str)
    ):
        return
    body = _load_json_mapping(_resolve_path(body_path, base_dir=base_dir), f"{prefix}.body", errors)
    header = _load_json_mapping(_resolve_path(header_path, base_dir=base_dir), f"{prefix}.header", errors)
    metadata = _load_json_mapping(_resolve_path(metadata_path, base_dir=base_dir), f"{prefix}.metadata", errors)
    proof_transactions = _load_json_list(
        _resolve_path(proof_transactions_path, base_dir=base_dir),
        f"{prefix}.proof_transactions",
        errors,
    )
    if proof is None or body is None or header is None or metadata is None or proof_transactions is None:
        return

    meta = proof.get("meta")
    if not isinstance(meta, Mapping):
        errors.append(f"{prefix}.proof.meta must be an object")
        return

    body_transactions = body.get("transactions")
    if not isinstance(body_transactions, list):
        errors.append(f"{prefix}.body.transactions must be a list")
        return

    _expect_hex_equal(
        binding.get("body_transactions_hash"),
        hash_v0("risc0_smoke_body_transactions_v0", body_transactions),
        f"{prefix}.body_transactions_hash",
        errors,
    )
    _expect_hex_equal(
        binding.get("proof_transactions_hash"),
        hash_v0("risc0_smoke_proof_transactions_v0", proof_transactions),
        f"{prefix}.proof_transactions_hash",
        errors,
    )
    if binding.get("proof_tx_count") != len(proof_transactions):
        errors.append(f"{prefix}.proof_tx_count mismatch")
    match_body = proof_transactions == body_transactions
    if binding.get("proof_transactions_match_body") is not match_body:
        errors.append(f"{prefix}.proof_transactions_match_body mismatch")
    projected_transactions = list(project_route_body_transactions_to_proof_v1(body_transactions))
    if projected_transactions != proof_transactions:
        errors.append(f"{prefix}.body_to_proof_projection rejected")
    if binding.get("body_to_proof_projection_checked") is not True:
        errors.append(f"{prefix}.body_to_proof_projection_checked mismatch")
    _validate_projection_contract_binding(binding, prefix=prefix, errors=errors)
    if risc0_cli_bin is not None:
        _validate_rust_txs_commitment(
            prefix=prefix,
            risc0_cli_bin=risc0_cli_bin,
            proof_transactions=proof_transactions,
            expected_txs_commitment=meta.get("txs_commitment"),
            errors=errors,
        )

    try:
        validate_header_body_roots_v0(dict(header), dict(body))
    except Exception as exc:  # noqa: BLE001
        errors.append(f"{prefix}.header_body_roots rejected: {exc}")

    try:
        validate_proof_metadata_header_binding_v0(dict(metadata), dict(header))
    except Exception as exc:  # noqa: BLE001
        errors.append(f"{prefix}.proof_metadata_header_binding rejected: {exc}")

    try:
        rebuilt = build_risc0_proof_metadata_v0(
            proof_envelope=proof,
            header=header,
            conflict_schedule_hash=str(metadata.get("conflict_schedule_hash")),
            feature_suite_hash=str(metadata.get("feature_suite_hash")),
            dependency_lock_hash=str(metadata.get("dependency_lock_hash")),
            toolchain_lock_hash=str(metadata.get("toolchain_lock_hash")),
            expected_execution_context_hash=str(
                proof.get("meta", {}).get("execution_context_hash", "")
            ),
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


def _validate_rust_txs_commitment(
    *,
    prefix: str,
    risc0_cli_bin: Path,
    proof_transactions: list[Any],
    expected_txs_commitment: Any,
    errors: list[str],
) -> None:
    if not isinstance(expected_txs_commitment, str):
        errors.append(f"{prefix}.proof.meta.txs_commitment must be a string")
        return
    request = {
        "schema": "tau_state_proof_txs_commitment",
        "schema_version": 1,
        "transactions": proof_transactions,
    }
    try:
        proc = subprocess.run(
            [str(risc0_cli_bin)],
            input=json.dumps(request, sort_keys=True, separators=(",", ":")),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=30,
            check=False,
        )
    except Exception as exc:  # noqa: BLE001
        errors.append(f"{prefix}.rust_txs_commitment command failed: {exc}")
        return
    if proc.returncode != 0:
        errors.append(
            f"{prefix}.rust_txs_commitment rejected: exit={proc.returncode} stderr={proc.stderr[-500:]}"
        )
        return
    try:
        out = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        errors.append(f"{prefix}.rust_txs_commitment invalid JSON: {exc}")
        return
    if not isinstance(out, Mapping):
        errors.append(f"{prefix}.rust_txs_commitment response must be an object")
        return
    if out.get("schema") != "tau_state_proof_txs_commitment_result":
        errors.append(f"{prefix}.rust_txs_commitment schema mismatch")
    if out.get("ok") is not True:
        errors.append(f"{prefix}.rust_txs_commitment ok must be true")
    if out.get("tx_count") != len(proof_transactions):
        errors.append(f"{prefix}.rust_txs_commitment tx_count mismatch")
    _expect_hex_equal(
        out.get("txs_commitment"),
        expected_txs_commitment,
        f"{prefix}.rust_txs_commitment",
        errors,
    )


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
        choices=sorted(ALLOWED_REQUIRED_CASES),
        help="Required case name. May be supplied more than once. Defaults to the full supported set.",
    )
    parser.add_argument("--pretty", action="store_true")
    parser.add_argument(
        "--risc0-cli-bin",
        type=Path,
        help="Optional tau-state-proof-risc0-cli binary used to recompute txs_commitment from proof_transactions_path.",
    )
    args = parser.parse_args(argv)

    check = validate_risc0_real_proof_smoke_report_v0(
        _load_json(args.report),
        required_cases=DEFAULT_REQUIRED_CASES if args.required_case is None else set(args.required_case),
        require_proof_files=bool(args.require_proof_files),
        risc0_cli_bin=args.risc0_cli_bin,
    )
    print(json.dumps(check, sort_keys=True, indent=2 if args.pretty else None))
    return 0 if check["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
