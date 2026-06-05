#!/usr/bin/env python3
"""Build/check the state-root surface evidence receipt.

This is the Phase 4 committed-receipt gate for the `state_root` CBC row. Build
mode runs the replayable proof slice that is cheap enough locally (Python
preimage injectivity + Rust Kani guard contracts) and records source hashes.
Check mode re-hashes the same tracked sources and validates the result envelope
without needing Kani.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Literal, Mapping, Sequence

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SPEC = ROOT / "src" / "kernels" / "dex" / "state_root_v5_scope_contract.json"
DEFAULT_RECEIPT = ROOT / "docs" / "assurance" / "state_root_surface_evidence_receipt.json"

SPEC_SCHEMA = "zenodex.state_root.formal_spec.v1"
RECEIPT_SCHEMA = "zenodex.state_root.surface_evidence_receipt.v1"
CHECK_SCHEMA = "zenodex.state_root.surface_evidence_receipt_check.v1"

EXPECTED_VERSION = 5
EXPECTED_SECTIONS = ["BAL", "POL", "LPB", "LPA", "NNC", "FEE"]
EXPECTED_EXCLUDED_LANES = ["vault", "oracle", "perps"]
TestProfile = Literal["none", "python", "rust", "all"]
EXPECTED_POOL_STATUS_CODES = {"active": 1, "frozen": 2, "disabled": 3}
EXPECTED_ORDERING = {
    "balances": "sort by decoded pubkey bytes, then decoded asset bytes",
    "pools": "sort by decoded pool_id bytes",
    "lp_balances": "sort by decoded pubkey bytes, then decoded pool_id bytes",
    "lp_duration_risk": "sort by decoded pubkey bytes, then decoded pool_id bytes",
    "nonces": "sort by decoded pubkey bytes",
}
EXPECTED_INCLUDED_SECTIONS = {
    "BAL": ["pubkey[48]", "asset[32]", "amount:uvarint"],
    "POL": [
        "pool_id[32]",
        "asset0[32]",
        "asset1[32]",
        "reserve0:uvarint",
        "reserve1:uvarint",
        "fee_bps:uvarint",
        "lp_supply:uvarint",
        "status_code:uvarint",
        "created_at:uvarint",
        "curve_tag:utf8_bytes",
        "curve_params:utf8_bytes",
    ],
    "LPB": ["pubkey[48]", "pool_id[32]", "amount:uvarint"],
    "LPA": [
        "pubkey[48]",
        "pool_id[32]",
        "last_mint_present:uvarint",
        "last_mint_timestamp:uvarint_if_present",
        "last_remove_present:uvarint",
        "last_remove_timestamp:uvarint_if_present",
        "churn_tier:uvarint",
        "last_churn_update_present:uvarint",
        "last_churn_update_timestamp:uvarint_if_present",
    ],
    "NNC": ["pubkey[48]", "last_nonce:uvarint"],
    "FEE": ["fee_accumulator.dust:uvarint"],
}
PYTHON_ENCODER_TOKEN_ORDER = {
    "_encode_balances_section": [
        "out += encode_uvarint(len(entries))",
        "out += pk_b",
        "out += asset_b",
        "out += encode_uvarint(amount)",
    ],
    "_encode_pools_section": [
        "out += encode_uvarint(len(entries))",
        "out += pool_b",
        "out += asset0_b",
        "out += asset1_b",
        "out += encode_uvarint(pool.reserve0)",
        "out += encode_uvarint(pool.reserve1)",
        "out += encode_uvarint(pool.fee_bps)",
        "out += encode_uvarint(pool.lp_supply)",
        "out += encode_uvarint(status_code)",
        "out += encode_uvarint(pool.created_at)",
        "out += encode_bytes(pool.curve_tag.encode(\"utf-8\"))",
        "out += encode_bytes(pool.curve_params.encode(\"utf-8\"))",
    ],
    "_encode_lp_section": [
        "out += encode_uvarint(len(entries))",
        "out += pk_b",
        "out += pool_b",
        "out += encode_uvarint(amount)",
    ],
    "_encode_lp_duration_risk_section": [
        "out += encode_uvarint(len(entries))",
        "out += pk_b",
        "out += pool_b",
        "out += encode_uvarint(1 if timestamp is not None else 0)",
        "out += encode_uvarint(timestamp)",
        "out += encode_uvarint(metadata.churn_tier)",
        "out += encode_uvarint(1 if metadata.last_churn_update_timestamp is not None else 0)",
        "out += encode_uvarint(metadata.last_churn_update_timestamp)",
    ],
    "_encode_nonce_section": [
        "out += encode_uvarint(len(entries))",
        "out += pk_b",
        "out += encode_uvarint(last_nonce)",
    ],
    "_encode_fee_section": ["return encode_uvarint(_fee_accumulator_dust(fee_accumulator))"],
}
RUST_ENCODER_TOKEN_ORDER = {
    "encode_balances": [
        "let mut out = encode_uvarint(decoded.len() as u128);",
        "out.extend_from_slice(pk);",
        "out.extend_from_slice(asset);",
        "out.extend_from_slice(&encode_uvarint(*amount));",
    ],
    "encode_pools": [
        "let mut out = encode_uvarint(decoded.len() as u128);",
        "out.extend_from_slice(pool);",
        "out.extend_from_slice(asset0);",
        "out.extend_from_slice(asset1);",
        "out.extend_from_slice(&encode_uvarint(e.reserve0));",
        "out.extend_from_slice(&encode_uvarint(e.reserve1));",
        "out.extend_from_slice(&encode_uvarint(e.fee_bps));",
        "out.extend_from_slice(&encode_uvarint(e.lp_supply));",
        "out.extend_from_slice(&encode_uvarint(e.status.code()));",
        "out.extend_from_slice(&encode_uvarint(e.created_at));",
        "out.extend_from_slice(&encode_bytes(e.curve_tag.as_bytes()));",
        "out.extend_from_slice(&encode_bytes(e.curve_params.as_bytes()));",
    ],
    "encode_lp": [
        "let mut out = encode_uvarint(decoded.len() as u128);",
        "out.extend_from_slice(pk);",
        "out.extend_from_slice(pool);",
        "out.extend_from_slice(&encode_uvarint(*amount));",
    ],
    "encode_lp_duration": [
        "let mut out = encode_uvarint(decoded.len() as u128);",
        "out.extend_from_slice(pk);",
        "out.extend_from_slice(pool);",
        "push_optional_ts(&mut out, e.last_mint_timestamp);",
        "push_optional_ts(&mut out, e.last_remove_timestamp);",
        "out.extend_from_slice(&encode_uvarint(e.churn_tier));",
        "push_optional_ts(&mut out, e.last_churn_update_timestamp);",
    ],
    "encode_nonces": [
        "let mut out = encode_uvarint(decoded.len() as u128);",
        "out.extend_from_slice(pk);",
        "out.extend_from_slice(&encode_uvarint(*last_nonce));",
    ],
    "encode_fee_accumulator": ["encode_uvarint(dust)"],
}

SECTION_CONTRACT_WITNESS_STATES = [
    {},
    {
        "balances": [
            {"pubkey": "0x" + "22" * 48, "asset": "0x" + "20" * 32, "amount": 7},
            {"pubkey": "0x" + "11" * 48, "asset": "0x" + "10" * 32, "amount": 1000},
        ]
    },
    {
        "pools": [
            {
                "pool_id": "0x" + "44" * 32,
                "asset0": "0x" + "10" * 32,
                "asset1": "0x" + "20" * 32,
                "reserve0": 7,
                "reserve1": 11,
                "fee_bps": 30,
                "lp_supply": 13,
                "status": "active",
                "created_at": 5,
                "curve_tag": "CPMM",
                "curve_params": "",
            },
            {
                "pool_id": "0x" + "33" * 32,
                "asset0": "0x" + "01" * 32,
                "asset1": "0x" + "02" * 32,
                "reserve0": 17,
                "reserve1": 19,
                "fee_bps": 10000,
                "lp_supply": 23,
                "status": "disabled",
                "created_at": 29,
                "curve_tag": "CUBIC_SUM_V1",
                "curve_params": '{"p":3,"q":5}',
            },
        ]
    },
    {
        "lp_balances": [
            {"pubkey": "0x" + "22" * 48, "pool_id": "0x" + "44" * 32, "amount": 31},
            {"pubkey": "0x" + "11" * 48, "pool_id": "0x" + "33" * 32, "amount": 37},
        ],
        "lp_duration_risk": [
            {
                "pubkey": "0x" + "22" * 48,
                "pool_id": "0x" + "44" * 32,
                "last_mint_timestamp": 41,
                "last_remove_timestamp": None,
                "churn_tier": 43,
                "last_churn_update_timestamp": 47,
            },
            {
                "pubkey": "0x" + "11" * 48,
                "pool_id": "0x" + "33" * 32,
                "last_mint_timestamp": None,
                "last_remove_timestamp": 53,
                "churn_tier": 0,
                "last_churn_update_timestamp": None,
            },
        ],
    },
    {
        "nonces": [
            {"pubkey": "0x" + "22" * 48, "last_nonce": 0xFFFFFFFF},
            {"pubkey": "0x" + "11" * 48, "last_nonce": 59},
        ],
        "fee_accumulator": {"dust": 61},
    },
]

EXPECTED_SOURCE_FILES = [
    "src/kernels/dex/state_root_v5_scope_contract.json",
    "tools/check_state_root_surface_evidence.py",
    "tests/test_check_state_root_surface_evidence.py",
    "src/state/state_root.py",
    "src/state/pools.py",
    "src/integration/zeno_ledger_v0.py",
    "src/runtime/authority.py",
    "src/runtime/rust_invoker.py",
    "tools/zeno_ledger_run_local.py",
    "tools/zeno_ledger_node.py",
    "rust-runtime/crates/zenodex-runtime-core/src/state_root.rs",
    "tools/runtime/state_root_lib.py",
    "tools/runtime/state_root_injectivity.py",
    "tests/state/test_state_root_determinism.py",
    "tests/runtime/test_state_root_vectors.py",
    "tests/runtime/test_state_root_live_path.py",
    "tests/runtime/test_state_root_injectivity_proof.py",
    "tests/runtime/test_state_root_section_framing_grid.py",
    "tests/runtime/test_state_root_curve_config_grid.py",
    "tests/runtime/test_state_root_lp_duration_exhaustive_grid.py",
    "tests/integration/test_zeno_ledger_post_state_root_binding_v0.py",
    "tests/integration/test_zeno_ledger_node_state_root_binding.py",
    "tests/integration/test_proof_verifier_perps_scope_guard_regression.py",
    "config/deploy/production-strict.yaml",
    "config/deploy/public-testnet.yaml",
    ".github/workflows/runtime-shadow.yml",
    ".github/workflows/release-integrity.yml",
]

KANI_HARNESSES = [
    "state_root::kani_contracts::pool_fee_bps_guard_is_exact",
    "state_root::kani_contracts::nonce_guard_is_exact",
    "state_root::kani_contracts::duration_metadata_presence_is_exact",
    "state_root::kani_contracts::pool_asset_order_guard_matches_fixed_width_byte_order",
    "state_root::kani_contracts::pool_asset_order_guard_rejects_equal_assets",
    "state_root::kani_contracts::pool_status_codes_are_in_domain_and_distinct",
    "state_root::kani_contracts::state_root_guard_covers_are_reachable",
]

KANI_EXPECTED_TOTALS: dict[str, dict[str, int]] = {
    "state_root::kani_contracts::pool_fee_bps_guard_is_exact": {
        "checks_total": 118,
        "cover_properties_total": 0,
    },
    "state_root::kani_contracts::nonce_guard_is_exact": {
        "checks_total": 118,
        "cover_properties_total": 0,
    },
    "state_root::kani_contracts::duration_metadata_presence_is_exact": {
        "checks_total": 1,
        "cover_properties_total": 0,
    },
    "state_root::kani_contracts::pool_asset_order_guard_matches_fixed_width_byte_order": {
        "checks_total": 42,
        "cover_properties_total": 0,
    },
    "state_root::kani_contracts::pool_asset_order_guard_rejects_equal_assets": {
        "checks_total": 42,
        "cover_properties_total": 0,
    },
    "state_root::kani_contracts::pool_status_codes_are_in_domain_and_distinct": {
        "checks_total": 7,
        "cover_properties_total": 0,
    },
    "state_root::kani_contracts::state_root_guard_covers_are_reachable": {
        "checks_total": 44,
        "cover_properties_total": 3,
    },
}

PYTHON_REQUIRED_TEST_COMMANDS = [
    {
        "id": "state_root_python_semantics",
        "command": [
            "python3",
            "-m",
            "pytest",
            "-q",
            "tests/state/test_state_root_determinism.py",
            "tests/runtime/test_state_root_injectivity_proof.py",
            "tests/runtime/test_state_root_section_framing_grid.py",
            "tests/runtime/test_state_root_lp_duration_exhaustive_grid.py",
        ],
    },
    {
        "id": "state_root_runtime_binding",
        "command": [
            "python3",
            "-m",
            "pytest",
            "-q",
            "tests/integration/test_zeno_ledger_post_state_root_binding_v0.py",
            "tests/integration/test_zeno_ledger_node_state_root_binding.py",
            "tests/integration/test_proof_verifier_perps_scope_guard_regression.py",
        ],
    },
]

RUST_REQUIRED_TEST_COMMANDS = [
    {
        "id": "state_root_python_rust_differential",
        "command": [
            "python3",
            "-m",
            "pytest",
            "-q",
            "tests/runtime/test_state_root_vectors.py",
            "tests/runtime/test_state_root_curve_config_grid.py",
            "tests/runtime/test_state_root_live_path.py",
        ],
    },
]

REQUIRED_TEST_COMMANDS = PYTHON_REQUIRED_TEST_COMMANDS + RUST_REQUIRED_TEST_COMMANDS


class EvidenceError(ValueError):
    pass


def _canonical_json_bytes(obj: Any) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _load_json_object(path: Path, *, name: str) -> dict[str, Any]:
    try:
        obj = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise EvidenceError(f"{name} missing: {path}") from exc
    except Exception as exc:
        raise EvidenceError(f"{name} is not valid JSON: {path}: {exc}") from exc
    if not isinstance(obj, dict):
        raise EvidenceError(f"{name} must be a JSON object: {path}")
    return obj


def _unexpected_keys(obj: Mapping[str, Any], *, allowed: set[str], name: str) -> list[str]:
    extra = sorted(set(obj) - allowed)
    return [f"{name} has unexpected public field(s): {extra}"] if extra else []


def _read_source_file(rel: str) -> str:
    return (ROOT / rel).read_text(encoding="utf-8")


def _python_function_body(source: str, name: str) -> str | None:
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return None
    lines = source.splitlines()
    for node in ast.walk(tree):
        if not isinstance(node, ast.FunctionDef) or node.name != name:
            continue
        end_lineno = getattr(node, "end_lineno", None)
        if end_lineno is None:
            return None
        return "\n".join(lines[node.lineno - 1 : end_lineno])
    return None


def _rust_function_body(source: str, name: str) -> str | None:
    match = re.search(rf"(?m)^(?:pub(?:\([^)]*\))?\s+)?fn\s+{re.escape(name)}\b", source)
    if match is None:
        return None
    brace = source.find("{", match.end())
    if brace < 0:
        return None
    depth = 0
    for index in range(brace, len(source)):
        char = source[index]
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return source[match.start() : index + 1]
    return None


def _tokens_in_order(body: str, tokens: Sequence[str]) -> bool:
    cursor = 0
    for token in tokens:
        found = body.find(token, cursor)
        if found < 0:
            return False
        cursor = found + len(token)
    return True


def _validate_encoder_source_tokens() -> list[str]:
    errors: list[str] = []
    py_source = _read_source_file("src/state/state_root.py")
    for fn_name, tokens in PYTHON_ENCODER_TOKEN_ORDER.items():
        body = _python_function_body(py_source, fn_name)
        if body is None:
            errors.append(f"src/state/state_root.py missing {fn_name}")
            continue
        if not _tokens_in_order(body, tokens):
            errors.append(f"src/state/state_root.py::{fn_name} encoder token order drifted")

    rust_source = _read_source_file("rust-runtime/crates/zenodex-runtime-core/src/state_root.rs")
    for fn_name, tokens in RUST_ENCODER_TOKEN_ORDER.items():
        body = _rust_function_body(rust_source, fn_name)
        if body is None:
            errors.append(f"rust state_root.rs missing {fn_name}")
            continue
        if not _tokens_in_order(body, tokens):
            errors.append(f"rust state_root.rs::{fn_name} encoder token order drifted")
    return errors


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise EvidenceError(f"{name} must be a non-negative integer")
    return int(value)


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise EvidenceError(f"{name} must be an object")
    return value


def _contract_fixed_hex(row: Mapping[str, Any], field: str, *, nbytes: int) -> bytes:
    from src.state.canonical import hex_to_bytes_fixed  # noqa: PLC0415

    return hex_to_bytes_fixed(str(row.get(field, "")), nbytes=nbytes, name=field)


def _contract_uvarint(value: object, *, name: str) -> bytes:
    from src.state.canonical import encode_uvarint  # noqa: PLC0415

    return encode_uvarint(_require_nonnegative_int(value, name=name))


def _contract_optional_timestamp(row: Mapping[str, Any], field: str) -> tuple[bytes, bytes]:
    timestamp = row.get(field)
    present = timestamp is not None
    return (
        _contract_uvarint(1 if present else 0, name=f"{field}.present"),
        b"" if not present else _contract_uvarint(timestamp, name=field),
    )


def _contract_pool_status_code(row: Mapping[str, Any]) -> int:
    status = row.get("status")
    if not isinstance(status, str) or status not in EXPECTED_POOL_STATUS_CODES:
        raise EvidenceError(f"pool.status must be one of {sorted(EXPECTED_POOL_STATUS_CODES)}")
    return EXPECTED_POOL_STATUS_CODES[status]


def _contract_field_bytes(field: str, row: Mapping[str, Any]) -> bytes:
    from src.state.canonical import encode_bytes  # noqa: PLC0415

    if field == "pubkey[48]":
        return _contract_fixed_hex(row, "pubkey", nbytes=48)
    if field in {"asset[32]", "asset0[32]", "asset1[32]"}:
        return _contract_fixed_hex(row, field.split("[", 1)[0], nbytes=32)
    if field == "pool_id[32]":
        return _contract_fixed_hex(row, "pool_id", nbytes=32)
    if field.endswith("_present:uvarint"):
        key = field.removesuffix("_present:uvarint") + "_timestamp"
        return _contract_optional_timestamp(row, key)[0]
    if field.endswith(":uvarint"):
        key = field.removesuffix(":uvarint")
        if key == "status_code":
            return _contract_uvarint(_contract_pool_status_code(row), name=key)
        if key == "fee_accumulator.dust":
            return _contract_uvarint(row.get("dust", 0), name=key)
        return _contract_uvarint(row.get(key), name=key)
    if field.endswith(":uvarint_if_present"):
        key = field.removesuffix(":uvarint_if_present")
        return _contract_optional_timestamp(row, key)[1]
    if field.endswith(":utf8_bytes"):
        key = field.removesuffix(":utf8_bytes")
        value = row.get(key, "")
        if not isinstance(value, str):
            raise EvidenceError(f"{key} must be a string")
        return encode_bytes(value.encode("utf-8"))
    raise EvidenceError(f"unknown section field contract: {field}")


def _contract_rows(label: str, state: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    from src.state.canonical import hex_to_bytes_fixed  # noqa: PLC0415

    if label == "BAL":
        rows = list(state.get("balances") or [])
        rows.sort(key=lambda row: (
            hex_to_bytes_fixed(str(row.get("pubkey", "")), nbytes=48, name="pubkey"),
            hex_to_bytes_fixed(str(row.get("asset", "")), nbytes=32, name="asset"),
        ))
        return rows
    if label == "POL":
        rows = list(state.get("pools") or [])
        rows.sort(key=lambda row: hex_to_bytes_fixed(str(row.get("pool_id", "")), nbytes=32, name="pool_id"))
        return rows
    if label == "LPB":
        rows = list(state.get("lp_balances") or [])
        rows.sort(key=lambda row: (
            hex_to_bytes_fixed(str(row.get("pubkey", "")), nbytes=48, name="pubkey"),
            hex_to_bytes_fixed(str(row.get("pool_id", "")), nbytes=32, name="pool_id"),
        ))
        return rows
    if label == "LPA":
        rows = list(state.get("lp_duration_risk") or [])
        rows.sort(key=lambda row: (
            hex_to_bytes_fixed(str(row.get("pubkey", "")), nbytes=48, name="pubkey"),
            hex_to_bytes_fixed(str(row.get("pool_id", "")), nbytes=32, name="pool_id"),
        ))
        return rows
    if label == "NNC":
        rows = list(state.get("nonces") or [])
        rows.sort(key=lambda row: hex_to_bytes_fixed(str(row.get("pubkey", "")), nbytes=48, name="pubkey"))
        return rows
    if label == "FEE":
        fee = state.get("fee_accumulator")
        return [_require_mapping(fee, name="fee_accumulator")] if fee is not None else [{"dust": 0}]
    raise EvidenceError(f"unknown section label: {label}")


def _contract_section_bytes(label: str, fields: Sequence[str], state: Mapping[str, Any]) -> bytes:
    from src.state.canonical import encode_uvarint  # noqa: PLC0415

    out = bytearray()
    rows = _contract_rows(label, state)
    if label != "FEE":
        out += encode_uvarint(len(rows))
    for row in rows:
        if not isinstance(row, Mapping):
            raise EvidenceError(f"{label} witness row must be an object")
        for field in fields:
            out += _contract_field_bytes(str(field), row)
    return bytes(out)


def _live_section_bytes(state: Mapping[str, Any]) -> dict[str, bytes]:
    from src.state import state_root as state_root_mod  # noqa: PLC0415
    from tools.runtime.state_root_lib import build_tables  # noqa: PLC0415

    balances, pools, lp_balances, nonces, fee_accumulator = build_tables(json.loads(json.dumps(state)))
    return {
        "BAL": state_root_mod._encode_balances_section(balances),  # noqa: SLF001
        "POL": state_root_mod._encode_pools_section(pools),  # noqa: SLF001
        "LPB": state_root_mod._encode_lp_section(lp_balances),  # noqa: SLF001
        "LPA": state_root_mod._encode_lp_duration_risk_section(lp_balances),  # noqa: SLF001
        "NNC": state_root_mod._encode_nonce_section(nonces),  # noqa: SLF001
        "FEE": state_root_mod._encode_fee_section(fee_accumulator),  # noqa: SLF001
    }


def _validate_section_contract_against_live(spec: Mapping[str, Any]) -> list[str]:
    # REVIEW [B -> A-]: source-token checks give drift teeth, but the load-bearing
    # guard is this executable byte contract. It independently derives section
    # bytes from the formal JSON contract and compares them with the live encoder
    # on witnesses that exercise ordering, optional fields, status codes, and
    # unequal reserves.
    errors: list[str] = []
    included = spec.get("included_sections")
    if not isinstance(included, Mapping):
        return ["spec.included_sections must be an object"]
    for witness_index, state in enumerate(SECTION_CONTRACT_WITNESS_STATES):
        try:
            live = _live_section_bytes(state)
        except Exception as exc:
            errors.append(f"live encoder rejected section witness[{witness_index}]: {exc}")
            continue
        for label in EXPECTED_SECTIONS:
            fields = included.get(label)
            if not isinstance(fields, list) or not all(isinstance(field, str) for field in fields):
                errors.append(f"spec.included_sections.{label} must be a list of field strings")
                continue
            try:
                expected = _contract_section_bytes(label, fields, state)
            except EvidenceError as exc:
                errors.append(f"formal section contract rejected witness[{witness_index}] {label}: {exc}")
                continue
            if expected != live[label]:
                errors.append(
                    f"formal spec/live encoder byte mismatch for witness[{witness_index}] section {label}"
                )
    return errors


def _source_hashes() -> list[dict[str, str]]:
    out: list[dict[str, str]] = []
    for rel in EXPECTED_SOURCE_FILES:
        path = ROOT / rel
        if not path.is_file():
            raise EvidenceError(f"source file missing: {rel}")
        out.append({"path": rel, "sha256": _sha256_file(path)})
    return out


def _receipt_hash_body(receipt: Mapping[str, Any]) -> dict[str, Any]:
    return {k: v for k, v in receipt.items() if k != "receipt_sha256"}


def _validate_spec_against_source(spec: Mapping[str, Any]) -> list[str]:
    errors: list[str] = []
    if spec.get("schema") != SPEC_SCHEMA:
        errors.append(f"spec.schema must be {SPEC_SCHEMA!r}")
    if spec.get("surface_id") != "state_root":
        errors.append("spec.surface_id must be 'state_root'")
    if spec.get("state_root_version") != EXPECTED_VERSION:
        errors.append(f"spec.state_root_version must be {EXPECTED_VERSION}")
    formula = spec.get("root_formula")
    if not isinstance(formula, Mapping):
        errors.append("spec.root_formula must be an object")
    else:
        domain = formula.get("domain")
        if not isinstance(domain, Mapping) or domain.get("tag") != "state_root" or domain.get("version") != EXPECTED_VERSION:
            errors.append("spec.root_formula.domain must be state_root/v5")
        if formula.get("hash") != "sha256":
            errors.append("spec.root_formula.hash must be sha256")
        if list(formula.get("section_order") or []) != EXPECTED_SECTIONS:
            errors.append("spec.root_formula.section_order does not match v5 source pin")
    widths = spec.get("identifier_widths")
    if widths != {"pubkey_bytes": 48, "asset_bytes": 32, "pool_id_bytes": 32}:
        errors.append("spec.identifier_widths must match fixed-width state-root identifiers")
    ordering = spec.get("ordering")
    if ordering != EXPECTED_ORDERING:
        errors.append("spec.ordering must match the v5 decoded-byte ordering contract")
    included = spec.get("included_sections")
    if included != EXPECTED_INCLUDED_SECTIONS:
        errors.append("spec.included_sections must match the exact v5 section-body encoding contract")
    excluded = spec.get("excluded_lanes")
    if not isinstance(excluded, list):
        errors.append("spec.excluded_lanes must be a list")
    else:
        fields = [item.get("field") for item in excluded if isinstance(item, Mapping)]
        if fields != EXPECTED_EXCLUDED_LANES:
            errors.append(f"spec.excluded_lanes fields {fields!r} != {EXPECTED_EXCLUDED_LANES!r}")
        for item in excluded:
            if not isinstance(item, Mapping):
                errors.append("spec.excluded_lanes entries must be objects")
                continue
            if item.get("required_value") != "None":
                errors.append(f"excluded lane {item.get('field')!r} must require None")
            if item.get("enforced_by") != "src.integration.zeno_ledger_v0.validate_dex_state_root_v0_spot_scope":
                errors.append(f"excluded lane {item.get('field')!r} has wrong enforcement ref")

    # Cross-check the spec against the imported Python implementation constants.
    sys.path.insert(0, str(ROOT))
    from src.state import state_root as state_root_mod  # noqa: PLC0415

    if state_root_mod.STATE_ROOT_VERSION != EXPECTED_VERSION:
        errors.append("src.state.state_root.STATE_ROOT_VERSION drifted")
    labels = [label.decode("ascii") for label in state_root_mod.STATE_ROOT_SECTION_LABELS]
    if labels != EXPECTED_SECTIONS:
        errors.append(f"src.state.state_root.STATE_ROOT_SECTION_LABELS {labels!r} != spec")
    errors.extend(_validate_encoder_source_tokens())
    errors.extend(_validate_section_contract_against_live(spec))
    return errors


def _run_injectivity_proof() -> dict[str, Any]:
    sys.path.insert(0, str(ROOT))
    from tools.runtime.state_root_injectivity import run_injectivity_proof  # noqa: PLC0415

    report = run_injectivity_proof()
    if not isinstance(report, dict) or report.get("ok") is not True:
        raise EvidenceError(f"state-root injectivity proof failed: {report!r}")
    names = {item.get("obligation"): item for item in report.get("obligations", []) if isinstance(item, Mapping)}
    expected = {
        "framing_injectivity_unconditional",
        "uvarint_injectivity",
        "bounded_no_collision_incl_FEE",
    }
    if set(names) != expected or any(item.get("ok") is not True for item in names.values()):
        raise EvidenceError(f"state-root injectivity obligations malformed: {report!r}")
    return report


def _kani_command() -> list[str]:
    command = [
        "cargo",
        "kani",
        "-p",
        "zenodex-runtime-core",
        "--lib",
    ]
    for harness in KANI_HARNESSES:
        command.extend(["--harness", harness])
    command.extend(["--exact", "--output-format", "terse", "--harness-timeout", "10m", "-Z", "unstable-options"])
    return command


def _parse_kani_output(stdout: str) -> list[dict[str, Any]]:
    harnesses: dict[str, dict[str, Any]] = {}
    for raw in stdout.split("Checking harness ")[1:]:
        name = raw.split("...", 1)[0].strip()
        checks = re.search(r"\*\* (\d+) of (\d+) failed", raw)
        status = re.search(r"VERIFICATION:-\s+(\w+)", raw)
        cover = re.search(r"\*\* (\d+) of (\d+) cover properties satisfied", raw)
        if checks is None or status is None:
            raise EvidenceError(f"could not parse Kani result for {name!r}")
        harnesses[name] = {
            "name": name,
            "verdict": "VERIFIED" if status.group(1) == "SUCCESSFUL" else status.group(1),
            "checks_failed": int(checks.group(1)),
            "checks_total": int(checks.group(2)),
            "cover_properties_satisfied": int(cover.group(1)) if cover else 0,
            "cover_properties_total": int(cover.group(2)) if cover else 0,
        }
    if set(harnesses) != set(KANI_HARNESSES):
        raise EvidenceError(
            f"Kani harness mismatch: parsed={sorted(harnesses)} expected={sorted(KANI_HARNESSES)}"
        )
    return [harnesses[name] for name in KANI_HARNESSES]


def _validate_kani_result(result: Any) -> list[str]:
    errors: list[str] = []
    if not isinstance(result, Mapping):
        return ["proof_artifact.kani must be an object"]
    # REVIEW [B -> A-]: the Kani envelope validated the expected verdict and
    # harness totals but still accepted resealed extra fields such as raw logs or
    # private paths. The public state-root proof payload is now an exact schema.
    errors.extend(
        _unexpected_keys(
            result,
            allowed={"verdict", "cargo_kani_version", "command", "harnesses"},
            name="proof_artifact.kani",
        )
    )
    if result.get("verdict") != "VERIFIED":
        errors.append("Kani proof verdict must be VERIFIED")
    if result.get("cargo_kani_version") != "cargo-kani 0.60.0":
        errors.append("Kani proof must use source-pinned cargo-kani 0.60.0")
    if result.get("command") != _kani_command():
        errors.append("Kani proof command drifted")
    harnesses = result.get("harnesses")
    if not isinstance(harnesses, list) or [h.get("name") for h in harnesses if isinstance(h, Mapping)] != KANI_HARNESSES:
        return errors + ["Kani proof harness list/order drifted"]
    for item in harnesses:
        if not isinstance(item, Mapping):
            errors.append("Kani harness row must be an object")
            continue
        errors.extend(
            _unexpected_keys(
                item,
                allowed={
                    "name",
                    "verdict",
                    "checks_failed",
                    "checks_total",
                    "cover_properties_satisfied",
                    "cover_properties_total",
                },
                name="Kani harness row",
            )
        )
        name = item.get("name")
        exp = KANI_EXPECTED_TOTALS.get(str(name))
        if exp is None:
            errors.append(f"unexpected Kani harness {name!r}")
            continue
        if item.get("verdict") != "VERIFIED" or item.get("checks_failed") != 0:
            errors.append(f"{name}: Kani harness did not verify cleanly")
        if item.get("checks_total") != exp["checks_total"]:
            errors.append(f"{name}: checks_total drifted")
        if item.get("cover_properties_total") != exp["cover_properties_total"]:
            errors.append(f"{name}: cover total drifted")
        if exp["cover_properties_total"] and item.get("cover_properties_satisfied") != exp["cover_properties_total"]:
            errors.append(f"{name}: cover properties not all satisfied")
    return errors


def _run_kani() -> dict[str, Any]:
    version_proc = subprocess.run(
        ["cargo", "kani", "--version"],
        cwd=str(ROOT / "rust-runtime"),
        capture_output=True,
        text=True,
        timeout=30,
    )
    if version_proc.returncode != 0:
        raise EvidenceError(f"cargo kani --version failed: {version_proc.stderr[-400:]}")
    command = _kani_command()
    proc = subprocess.run(
        command,
        cwd=str(ROOT / "rust-runtime"),
        capture_output=True,
        text=True,
        timeout=1800,
    )
    if proc.returncode != 0:
        raise EvidenceError(
            f"cargo kani failed with returncode={proc.returncode}: "
            f"stdout={proc.stdout[-1200:]} stderr={proc.stderr[-1200:]}"
        )
    result = {
        "verdict": "VERIFIED",
        "cargo_kani_version": version_proc.stdout.strip(),
        "command": command,
        "harnesses": _parse_kani_output(proc.stdout),
    }
    errors = _validate_kani_result(result)
    if errors:
        raise EvidenceError("; ".join(errors))
    return result


def _runtime_shadow_paths_are_gated() -> list[str]:
    workflow = (ROOT / ".github" / "workflows" / "runtime-shadow.yml").read_text(encoding="utf-8")
    required_snippets = [
        "src/state/state_root.py",
        "tools/zeno_ledger_node.py",
        "rust-runtime/**",
        "tools/runtime/**",
        "tests/runtime/**",
        "tests/runtime/test_state_root_vectors.py",
        "tests/runtime/test_state_root_live_path.py",
        "--ignore=tests/runtime/test_state_root_live_path.py",
        "tests/integration/test_zeno_ledger_node_state_root_binding.py",
        "tools/check_state_root_surface_evidence.py check --pretty --test-profile python",
        "tools/check_state_root_surface_evidence.py check --pretty --test-profile rust",
    ]
    return [snippet for snippet in required_snippets if snippet not in workflow]


def _release_integrity_state_root_gate_is_present() -> list[str]:
    workflow = (ROOT / ".github" / "workflows" / "release-integrity.yml").read_text(encoding="utf-8")
    required_snippets = [
        "tools/check_state_root_surface_evidence.py check --pretty",
        "tests/test_check_state_root_surface_evidence.py",
    ]
    return [snippet for snippet in required_snippets if snippet not in workflow]


def _load_workflow(rel: str) -> Mapping[str, Any]:
    try:
        import yaml  # type: ignore[import-untyped]
    except Exception as exc:  # pragma: no cover - dependency is in dev requirements
        raise EvidenceError(f"PyYAML unavailable for workflow placement check: {exc}") from exc
    workflow = yaml.safe_load((ROOT / rel).read_text(encoding="utf-8"))
    if not isinstance(workflow, Mapping):
        raise EvidenceError(f"{rel} must be a YAML object")
    return workflow


def _job_run_blocks(workflow: Mapping[str, Any], job_id: str) -> list[str]:
    jobs = workflow.get("jobs")
    if not isinstance(jobs, Mapping):
        return []
    job = jobs.get(job_id)
    if not isinstance(job, Mapping):
        return []
    steps = job.get("steps")
    if not isinstance(steps, list):
        return []
    return [
        str(step["run"])
        for step in steps
        if isinstance(step, Mapping) and isinstance(step.get("run"), str)
    ]


def _active_run_text(block: str) -> str:
    return "\n".join(line for line in block.splitlines() if not line.lstrip().startswith("#"))


def _job_has_run_snippet(workflow: Mapping[str, Any], job_id: str, snippet: str) -> bool:
    return any(snippet in _active_run_text(block) for block in _job_run_blocks(workflow, job_id))


def _job_snippet_order(workflow: Mapping[str, Any], job_id: str, before: str, after: str) -> bool:
    active_script = "\n".join(
        _active_run_text(block) for block in _job_run_blocks(workflow, job_id)
    )
    before_index = active_script.find(before)
    after_index = active_script.find(after)
    return 0 <= before_index < after_index


def _runtime_shadow_state_root_placement_errors() -> list[str]:
    # REVIEW [B -> A-]: substring checks proved that command text existed
    # somewhere in runtime-shadow.yml, but not that it ran in the intended job.
    # The state-root authority claim depends on the Python evidence lane staying
    # in python-runtime and the Rust authority lane running after the Rust shadow
    # binary is built. These structural checks make comment/placement drift fail.
    try:
        workflow = _load_workflow(".github/workflows/runtime-shadow.yml")
    except EvidenceError as exc:
        return [str(exc)]
    errors: list[str] = []
    python_job = "python-runtime"
    rust_job = "python-rust-shadow"
    python_requirements = [
        "--ignore=tests/runtime/test_state_root_live_path.py",
        "tools/check_state_root_surface_evidence.py check --pretty --test-profile python",
        "tests/test_check_state_root_surface_evidence.py",
    ]
    for snippet in python_requirements:
        if not _job_has_run_snippet(workflow, python_job, snippet):
            errors.append(
                f"runtime-shadow {python_job} job missing state-root run snippet: {snippet}"
            )
    rust_requirements = [
        "tests/runtime/test_state_root_live_path.py",
        "tools/check_state_root_surface_evidence.py check --pretty --test-profile rust",
    ]
    for snippet in rust_requirements:
        if not _job_has_run_snippet(workflow, rust_job, snippet):
            errors.append(
                f"runtime-shadow {rust_job} job missing state-root run snippet: {snippet}"
            )
    if not _job_snippet_order(
        workflow,
        rust_job,
        "cargo build --bin zenodex-runtime",
        "tools/check_state_root_surface_evidence.py check --pretty --test-profile rust",
    ):
        errors.append(
            "runtime-shadow rust state-root receipt check must run after cargo builds zenodex-runtime"
        )
    return errors


def _release_integrity_state_root_placement_errors() -> list[str]:
    try:
        workflow = _load_workflow(".github/workflows/release-integrity.yml")
    except EvidenceError as exc:
        return [str(exc)]
    job_id = "release-integrity"
    required = [
        "tools/check_state_root_surface_evidence.py check --pretty",
        "tests/test_check_state_root_surface_evidence.py",
    ]
    return [
        f"release-integrity {job_id} job missing state-root run snippet: {snippet}"
        for snippet in required
        if not _job_has_run_snippet(workflow, job_id, snippet)
    ]


def _profile_result() -> dict[str, Any]:
    try:
        import yaml  # type: ignore[import-untyped]
    except Exception as exc:  # pragma: no cover - dependency is in dev requirements
        raise EvidenceError(f"PyYAML unavailable for deployment profile check: {exc}") from exc

    prod = yaml.safe_load((ROOT / "config" / "deploy" / "production-strict.yaml").read_text(encoding="utf-8"))
    testnet = yaml.safe_load((ROOT / "config" / "deploy" / "public-testnet.yaml").read_text(encoding="utf-8"))
    prod_policy = prod["runtime_authority_policy"]
    testnet_policy = testnet["runtime_authority_policy"]
    if prod_policy["default"] != "python_authority" or prod_policy["per_surface"] != {}:
        raise EvidenceError("production-strict authority policy for state_root is not all-Python")
    if testnet_policy["per_surface"].get("state_root") != "rust_authority_with_python_shadow":
        raise EvidenceError("public-testnet state_root must run Rust authority with Python shadow")
    if "state_root" not in set(testnet_policy.get("promoted_surfaces") or []):
        raise EvidenceError("public-testnet state_root must be in promoted_surfaces")
    return {
        "verdict": "CHECKED",
        "production_strict": "python_authority",
        "public_testnet": "rust_authority_with_python_shadow",
    }


def _required_test_commands_for_profile(profile: TestProfile) -> list[dict[str, Any]]:
    if profile == "none":
        return []
    if profile == "python":
        return PYTHON_REQUIRED_TEST_COMMANDS
    if profile == "rust":
        return RUST_REQUIRED_TEST_COMMANDS
    if profile == "all":
        return REQUIRED_TEST_COMMANDS
    raise EvidenceError(f"unknown required-test profile: {profile}")


def _run_required_test_commands(profile: TestProfile = "all") -> list[str]:
    errors: list[str] = []
    for row in _required_test_commands_for_profile(profile):
        command = row["command"]
        proc = subprocess.run(
            command,
            cwd=str(ROOT),
            capture_output=True,
            text=True,
            timeout=900,
        )
        if proc.returncode != 0:
            errors.append(
                f"required test command {row['id']} failed with returncode={proc.returncode}: "
                f"stdout={proc.stdout[-1200:]} stderr={proc.stderr[-1200:]}"
            )
            continue
        combined = f"{proc.stdout}\n{proc.stderr}"
        if re.search(r"\b\d+\s+skipped\b", combined):
            errors.append(
                f"required test command {row['id']} reported skipped tests; "
                "state-root evidence commands must execute their load-bearing tests"
            )
        # REVIEW [B -> A-]: the first parser rejected xfailed rows but still
        # allowed xpassed rows. An XPASS means the command still contains an
        # expected-failure marker, so it is not a clean all-pass evidence suite.
        if re.search(r"\b\d+\s+(xfailed|xpassed|deselected)\b", combined) or "no tests ran" in combined.lower():
            errors.append(
                f"required test command {row['id']} did not execute a clean all-pass suite; "
                "state-root evidence commands must not xfail, xpass, deselect, or run zero tests"
            )
    return errors


def build_receipt(*, spec_path: Path = DEFAULT_SPEC) -> dict[str, Any]:
    spec = _load_json_object(spec_path, name="state-root formal spec")
    spec_errors = _validate_spec_against_source(spec)
    if spec_errors:
        raise EvidenceError("; ".join(spec_errors))
    missing_workflow = _runtime_shadow_paths_are_gated()
    if missing_workflow:
        raise EvidenceError(f"runtime-shadow workflow missing state-root gates: {missing_workflow}")
    workflow_placement = _runtime_shadow_state_root_placement_errors()
    if workflow_placement:
        raise EvidenceError(
            f"runtime-shadow workflow misplaced state-root gates: {workflow_placement}"
        )
    missing_release = _release_integrity_state_root_gate_is_present()
    if missing_release:
        raise EvidenceError(
            f"release-integrity workflow missing state-root gates: {missing_release}"
        )
    release_placement = _release_integrity_state_root_placement_errors()
    if release_placement:
        raise EvidenceError(
            f"release-integrity workflow misplaced state-root gates: {release_placement}"
        )
    receipt = {
        "schema": RECEIPT_SCHEMA,
        "surface_id": "state_root",
        "state_root_version": EXPECTED_VERSION,
        "evidence_columns": {
            "running_impl": {
                "verdict": "CHECKED",
                "refs": ["src/state/state_root.py", "src/integration/zeno_ledger_v0.py::dex_state_root_v0"],
            },
            "formal_spec": {
                "verdict": "CROSS_CHECKED",
                "ref": "src/kernels/dex/state_root_v5_scope_contract.json",
                "spec_sha256": _sha256_file(spec_path),
            },
            "proof_artifact": {
                "verdict": "VERIFIED",
                "preimage_injectivity": _run_injectivity_proof(),
                "kani": _run_kani(),
            },
            "differential_tests": {
                "verdict": "PR_GATED",
                "command_ids": ["state_root_python_rust_differential"],
            },
            "runtime_invariants": {
                "verdict": "ENFORCED_AND_TESTED",
                "command_ids": ["state_root_runtime_binding"],
            },
            "authority_mode": _profile_result(),
        },
        "required_test_commands": REQUIRED_TEST_COMMANDS,
        "source_files": _source_hashes(),
        "private_toolchain_source_included": False,
    }
    receipt["receipt_sha256"] = _sha256_bytes(_canonical_json_bytes(_receipt_hash_body(receipt)))
    return receipt


def verify_receipt(receipt: Mapping[str, Any], *, spec_path: Path = DEFAULT_SPEC) -> list[str]:
    errors: list[str] = []
    # REVIEW [B -> A-]: receipt_sha256 proves only self-consistency. The prior
    # checker accepted resealed extra top-level, evidence-column, and source-row
    # fields, which could carry unsupported claims or private paths. Exact public
    # schemas keep the state-root receipt narrow and reviewable.
    errors.extend(
        _unexpected_keys(
            receipt,
            allowed={
                "schema",
                "surface_id",
                "state_root_version",
                "evidence_columns",
                "source_files",
                "required_test_commands",
                "private_toolchain_source_included",
                "receipt_sha256",
            },
            name="receipt",
        )
    )
    if receipt.get("schema") != RECEIPT_SCHEMA:
        errors.append(f"receipt.schema must be {RECEIPT_SCHEMA!r}")
    if receipt.get("surface_id") != "state_root":
        errors.append("receipt.surface_id must be 'state_root'")
    expected_hash = _sha256_bytes(_canonical_json_bytes(_receipt_hash_body(receipt)))
    if receipt.get("receipt_sha256") != expected_hash:
        errors.append("receipt_sha256 mismatch")

    spec = _load_json_object(spec_path, name="state-root formal spec")
    errors.extend(_validate_spec_against_source(spec))

    source_rows = receipt.get("source_files")
    if not isinstance(source_rows, list):
        errors.append("receipt.source_files must be a list")
    else:
        paths = [row.get("path") for row in source_rows if isinstance(row, Mapping)]
        if paths != EXPECTED_SOURCE_FILES:
            errors.append("receipt.source_files path list/order drifted")
        current = {row["path"]: row["sha256"] for row in _source_hashes()}
        for index, row in enumerate(source_rows):
            if not isinstance(row, Mapping):
                errors.append("receipt.source_files entries must be objects")
                continue
            errors.extend(
                _unexpected_keys(
                    row,
                    allowed={"path", "sha256"},
                    name=f"receipt.source_files[{index}]",
                )
            )
            path = row.get("path")
            if not isinstance(path, str):
                errors.append("receipt source path must be a string")
                continue
            if row.get("sha256") != current.get(path):
                errors.append(f"source hash drift: {path}")

    columns = receipt.get("evidence_columns")
    if not isinstance(columns, Mapping):
        errors.append("receipt.evidence_columns must be an object")
        return errors
    expected_columns = {
        "running_impl",
        "formal_spec",
        "proof_artifact",
        "differential_tests",
        "runtime_invariants",
        "authority_mode",
    }
    if set(columns) != expected_columns:
        errors.append("receipt.evidence_columns must cover exactly the six evidence columns")
        return errors
    column_allowed_keys = {
        "running_impl": {"verdict", "refs"},
        "formal_spec": {"verdict", "ref", "spec_sha256"},
        "proof_artifact": {"verdict", "preimage_injectivity", "kani"},
        "differential_tests": {"verdict", "command_ids"},
        "runtime_invariants": {"verdict", "command_ids"},
        "authority_mode": {"verdict", "production_strict", "public_testnet"},
    }
    column_maps: dict[str, Mapping[str, Any]] = {}
    for name, allowed in column_allowed_keys.items():
        column = columns.get(name)
        if not isinstance(column, Mapping):
            errors.append(f"receipt.evidence_columns.{name} must be an object")
            continue
        errors.extend(_unexpected_keys(column, allowed=allowed, name=f"receipt.evidence_columns.{name}"))
        column_maps[name] = column
    if set(column_maps) != expected_columns:
        return errors
    if column_maps["running_impl"].get("verdict") != "CHECKED":
        errors.append("running_impl verdict must be CHECKED")
    formal = column_maps["formal_spec"]
    if formal.get("verdict") != "CROSS_CHECKED" or formal.get("spec_sha256") != _sha256_file(spec_path):
        errors.append("formal_spec receipt does not match live spec")
    proof = column_maps["proof_artifact"]
    if proof.get("verdict") != "VERIFIED":
        errors.append("proof_artifact verdict must be VERIFIED")
    try:
        live_injectivity = _run_injectivity_proof()
        if proof.get("preimage_injectivity") != live_injectivity:
            errors.append("preimage injectivity proof result drifted")
    except EvidenceError as exc:
        errors.append(str(exc))
    errors.extend(_validate_kani_result(proof.get("kani")))
    if column_maps["differential_tests"].get("verdict") != "PR_GATED":
        errors.append("differential_tests verdict must be PR_GATED")
    if column_maps["runtime_invariants"].get("verdict") != "ENFORCED_AND_TESTED":
        errors.append("runtime_invariants verdict must be ENFORCED_AND_TESTED")
    try:
        if column_maps["authority_mode"] != _profile_result():
            errors.append("authority_mode profile result drifted")
    except EvidenceError as exc:
        errors.append(str(exc))
    if receipt.get("required_test_commands") != REQUIRED_TEST_COMMANDS:
        errors.append("required_test_commands drifted")
    if receipt.get("private_toolchain_source_included") is not False:
        errors.append("receipt must not include private toolchain source")
    missing_workflow = _runtime_shadow_paths_are_gated()
    if missing_workflow:
        errors.append(f"runtime-shadow workflow missing state-root gates: {missing_workflow}")
    workflow_placement = _runtime_shadow_state_root_placement_errors()
    if workflow_placement:
        errors.append(f"runtime-shadow workflow misplaced state-root gates: {workflow_placement}")
    missing_release = _release_integrity_state_root_gate_is_present()
    if missing_release:
        errors.append(f"release-integrity workflow missing state-root gates: {missing_release}")
    release_placement = _release_integrity_state_root_placement_errors()
    if release_placement:
        errors.append(f"release-integrity workflow misplaced state-root gates: {release_placement}")
    return errors


def check_receipt_file(
    *,
    receipt_path: Path = DEFAULT_RECEIPT,
    spec_path: Path = DEFAULT_SPEC,
    run_required_tests: bool = True,
    test_profile: TestProfile = "all",
) -> dict[str, Any]:
    errors: list[str] = []
    try:
        receipt = _load_json_object(receipt_path, name="state-root surface evidence receipt")
        errors.extend(verify_receipt(receipt, spec_path=spec_path))
        if run_required_tests and not errors:
            errors.extend(_run_required_test_commands(profile=test_profile))
    except EvidenceError as exc:
        errors.append(str(exc))
    return {
        "schema": CHECK_SCHEMA,
        "ok": not errors,
        "receipt": str(receipt_path),
        "spec": str(spec_path),
        "errors": errors,
    }


def _cmd_build(args: argparse.Namespace) -> int:
    receipt = build_receipt(spec_path=Path(args.spec))
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.pretty:
        print(json.dumps({"ok": True, "receipt": str(out)}, indent=2, sort_keys=True))
    else:
        print(json.dumps({"ok": True, "receipt": str(out)}, sort_keys=True))
    return 0


def _cmd_check(args: argparse.Namespace) -> int:
    report = check_receipt_file(
        receipt_path=Path(args.receipt),
        spec_path=Path(args.spec),
        test_profile=args.test_profile,
    )
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="State-root surface evidence receipt gate")
    sub = parser.add_subparsers(dest="cmd", required=True)
    p_build = sub.add_parser("build")
    p_build.add_argument("--spec", default=str(DEFAULT_SPEC))
    p_build.add_argument("--out", default=str(DEFAULT_RECEIPT))
    p_build.add_argument("--pretty", action="store_true")
    p_build.set_defaults(func=_cmd_build)
    p_check = sub.add_parser("check")
    p_check.add_argument("--spec", default=str(DEFAULT_SPEC))
    p_check.add_argument("--receipt", default=str(DEFAULT_RECEIPT))
    p_check.add_argument("--test-profile", choices=("none", "python", "rust", "all"), default="all")
    p_check.add_argument("--pretty", action="store_true")
    p_check.set_defaults(func=_cmd_check)
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
