#!/usr/bin/env python3
"""Validate recursive lifecycle proof admission packets.

This checker is the deterministic fallback for the Tau admission contract
`recursive_lifecycle_asset_delta_admission_v1`. It recomputes recursive
asset-delta row roots, checks aggregate row conservation, checks authority
roots, and binds the recursive journal metadata to a header context before a
recursive lifecycle proof can be treated as admissible.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping

PACKET_SCHEMA = "zenodex.recursive_lifecycle_admission_packet.v1"
REPORT_SCHEMA = "zenodex.recursive_lifecycle_admission_report.v1"

PROOF_TYPE_RECURSIVE = "risc0.zenodex_recursive_epoch.v1"
PROOF_PROFILE_RECURSIVE = "recursive_epoch_v1"

ASSET_DELTA_ROOT_DOMAIN = b"zenodex.risc0.recursive.asset_delta_root.v1"
ZERO32 = "0" * 64
U128_MAX = (1 << 128) - 1

HEADER_BOUND_ROOT_FIELDS = (
    "post_state_root",
    "tx_root",
    "evidence_root",
    "receipt_root",
    "aggregate_asset_delta_root",
    "data_availability_root",
    "public_policy_hash",
    "feature_suite_hash",
)


def validate_recursive_lifecycle_admission_packet_v1(packet: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(packet, "packet", errors)
    if obj.get("schema") != PACKET_SCHEMA:
        errors.append("schema mismatch")

    tau_inputs = _proof_gate_inputs(obj, errors)
    meta = _mapping(obj.get("proof_meta"), "proof_meta", errors)
    header = _mapping(obj.get("header"), "header", errors)
    row_count, row_root, meta_root, binding_inputs = _asset_delta_binding_inputs(obj, meta, header, errors)
    tau_inputs.update(binding_inputs)
    child_count_ok = _positive_int(meta.get("child_count"), "proof_meta.child_count", errors) is not None

    verdict = child_count_ok and all(tau_inputs.values())

    return {
        "schema": REPORT_SCHEMA,
        "ok": verdict and not errors,
        "status": "accepted" if verdict and not errors else "rejected",
        "errors": errors,
        "tau_inputs": tau_inputs,
        "row_count": row_count,
        "computed_aggregate_asset_delta_root": row_root,
        "expected_aggregate_asset_delta_root": meta_root,
    }


def _proof_gate_inputs(obj: Mapping[str, Any], errors: list[str]) -> dict[str, bool]:
    proof_type = _str(obj.get("proof_type"), "proof_type", errors)
    proof_profile = _str(obj.get("proof_profile"), "proof_profile", errors)
    proof_profile_supported = proof_type == PROOF_TYPE_RECURSIVE and proof_profile == PROOF_PROFILE_RECURSIVE
    if not proof_profile_supported:
        errors.append("proof profile unsupported")
    return {
        "proof_requested": _true(obj.get("proof_requested"), "proof_requested", errors),
        "proof_verified": _true(obj.get("proof_verified"), "proof_verified", errors),
        "proof_profile_supported": proof_profile_supported,
        "unsupported_lifecycle_absent": _true(
            obj.get("unsupported_lifecycle_absent"),
            "unsupported_lifecycle_absent",
            errors,
        ),
    }


def _asset_delta_binding_inputs(
    obj: Mapping[str, Any],
    meta: Mapping[str, Any],
    header: Mapping[str, Any],
    errors: list[str],
) -> tuple[int, str | None, str | None, dict[str, bool]]:
    rows = _asset_delta_rows(obj.get("asset_delta_rows"), errors)
    allowed_authorities = _hex32_set(obj.get("allowed_authority_roots"), "allowed_authority_roots", errors)

    row_root = _asset_delta_root(rows, errors) if rows is not None else None
    meta_root = _hex32(meta.get("aggregate_asset_delta_root"), "proof_meta.aggregate_asset_delta_root", errors)
    header_root = _hex32(header.get("aggregate_asset_delta_root"), "header.aggregate_asset_delta_root", errors)
    asset_delta_root_bound = row_root is not None and row_root == meta_root == header_root
    if not asset_delta_root_bound:
        errors.append("asset_delta_root binding mismatch")

    row_count = 0 if rows is None else len(rows)
    aggregate_rows_balanced = _aggregate_rows_balanced(rows, errors) if rows is not None else False
    authority_roots_allowed = _authority_roots_allowed(rows, allowed_authorities, errors) if rows is not None else False
    return (
        row_count,
        row_root,
        meta_root,
        {
            "leaf_rows_derived": row_root is not None,
            "asset_delta_root_bound": asset_delta_root_bound,
            "aggregate_rows_balanced": aggregate_rows_balanced,
            "authority_roots_allowed": authority_roots_allowed,
            "tau_header_binding_ok": _header_binding_ok(meta, header, errors),
            "transcript_binding_ok": _transcript_binding_ok(obj, errors),
        },
    )


def _asset_delta_root(rows: list[Mapping[str, Any]], errors: list[str]) -> str | None:
    if not _rows_sorted_unique(rows, errors):
        return None
    h = hashlib.sha256()
    h.update(ASSET_DELTA_ROOT_DOMAIN)
    h.update(len(rows).to_bytes(4, "big"))
    for row in rows:
        asset_id = str(row["asset_id"])
        raw_asset = asset_id.encode("utf-8")
        h.update(len(raw_asset).to_bytes(4, "big"))
        h.update(raw_asset)
        for field in (
            "debit_atoms",
            "credit_atoms",
            "authorized_mint_atoms",
            "authorized_burn_atoms",
        ):
            h.update(int(row[field]).to_bytes(16, "big"))
        h.update(bytes.fromhex(str(row["authority_root"])))
    return h.hexdigest()


def _asset_delta_rows(value: Any, errors: list[str]) -> list[Mapping[str, Any]] | None:
    if not isinstance(value, list):
        errors.append("asset_delta_rows must be a list")
        return None
    rows: list[Mapping[str, Any]] = []
    for index, raw in enumerate(value):
        row_errors: list[str] = []
        row = _mapping(raw, f"asset_delta_rows[{index}]", row_errors)
        asset_id = _str(row.get("asset_id"), f"asset_delta_rows[{index}].asset_id", row_errors)
        if asset_id == "":
            row_errors.append(f"asset_delta_rows[{index}].asset_id must be non-empty")
        parsed = {
            "asset_id": asset_id,
            "debit_atoms": _u128(row.get("debit_atoms"), f"asset_delta_rows[{index}].debit_atoms", row_errors),
            "credit_atoms": _u128(row.get("credit_atoms"), f"asset_delta_rows[{index}].credit_atoms", row_errors),
            "authorized_mint_atoms": _u128(
                row.get("authorized_mint_atoms"),
                f"asset_delta_rows[{index}].authorized_mint_atoms",
                row_errors,
            ),
            "authorized_burn_atoms": _u128(
                row.get("authorized_burn_atoms"),
                f"asset_delta_rows[{index}].authorized_burn_atoms",
                row_errors,
            ),
            "authority_root": _hex32(
                row.get("authority_root"),
                f"asset_delta_rows[{index}].authority_root",
                row_errors,
            ),
        }
        if row_errors:
            errors.extend(row_errors)
            continue
        rows.append(parsed)
    return rows


def _rows_sorted_unique(rows: list[Mapping[str, Any]], errors: list[str]) -> bool:
    prev: str | None = None
    ok = True
    for row in rows:
        asset_id = str(row["asset_id"])
        if prev is not None and asset_id <= prev:
            errors.append("asset_delta_rows must be sorted by unique asset_id")
            ok = False
            break
        prev = asset_id
    return ok


def _aggregate_rows_balanced(rows: list[Mapping[str, Any]], errors: list[str]) -> bool:
    ok = True
    for row in rows:
        debit_side = int(row["debit_atoms"]) + int(row["authorized_mint_atoms"])
        credit_side = int(row["credit_atoms"]) + int(row["authorized_burn_atoms"])
        if debit_side != credit_side:
            errors.append(f"aggregate row unbalanced: {row['asset_id']}")
            ok = False
    return ok


def _authority_roots_allowed(
    rows: list[Mapping[str, Any]],
    allowed_authorities: set[str],
    errors: list[str],
) -> bool:
    ok = True
    for row in rows:
        authority = str(row["authority_root"])
        has_authorized_effect = int(row["authorized_mint_atoms"]) != 0 or int(row["authorized_burn_atoms"]) != 0
        if has_authorized_effect:
            if authority == ZERO32:
                errors.append(f"asset authority root zero: {row['asset_id']}")
                ok = False
            elif authority not in allowed_authorities:
                errors.append(f"asset authority root not allowed: {row['asset_id']}")
                ok = False
        elif authority != ZERO32:
            errors.append(f"asset authority root unexpected: {row['asset_id']}")
            ok = False
    return ok


def _header_binding_ok(meta: Mapping[str, Any], header: Mapping[str, Any], errors: list[str]) -> bool:
    ok = True
    for field in HEADER_BOUND_ROOT_FIELDS:
        meta_value = _hex32(meta.get(field), f"proof_meta.{field}", errors)
        header_value = _hex32(header.get(field), f"header.{field}", errors)
        if meta_value != header_value:
            errors.append(f"header binding mismatch: {field}")
            ok = False
        elif meta_value == ZERO32:
            errors.append(f"header binding zero root: {field}")
            ok = False
    return ok


def _transcript_binding_ok(obj: Mapping[str, Any], errors: list[str]) -> bool:
    actual = _hex32(obj.get("transcript_binding_hash"), "transcript_binding_hash", errors)
    expected = _hex32(obj.get("expected_transcript_binding_hash"), "expected_transcript_binding_hash", errors)
    if actual != expected:
        errors.append("transcript binding mismatch")
        return False
    if actual == ZERO32:
        errors.append("transcript binding hash zero")
        return False
    return True


def _hex32_set(value: Any, name: str, errors: list[str]) -> set[str]:
    if not isinstance(value, list):
        errors.append(f"{name} must be a list")
        return set()
    out: set[str] = set()
    for index, item in enumerate(value):
        parsed = _hex32(item, f"{name}[{index}]", errors)
        if parsed is not None:
            out.add(parsed)
    return out


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if isinstance(value, Mapping):
        return value
    errors.append(f"{name} must be an object")
    return {}


def _str(value: Any, name: str, errors: list[str]) -> str | None:
    if isinstance(value, str):
        return value
    errors.append(f"{name} must be a string")
    return None


def _true(value: Any, name: str, errors: list[str]) -> bool:
    if value is True:
        return True
    errors.append(f"{name} must be true")
    return False


def _positive_int(value: Any, name: str, errors: list[str]) -> int | None:
    if isinstance(value, bool) or not isinstance(value, int):
        errors.append(f"{name} must be a positive integer")
        return None
    if value <= 0:
        errors.append(f"{name} must be a positive integer")
        return None
    return value


def _u128(value: Any, name: str, errors: list[str]) -> int | None:
    if isinstance(value, str) and value.isdecimal():
        parsed = int(value)
    elif isinstance(value, int) and not isinstance(value, bool):
        parsed = value
    else:
        errors.append(f"{name} must be a u128 decimal")
        return None
    if parsed < 0 or parsed > U128_MAX:
        errors.append(f"{name} out of u128 range")
        return None
    return parsed


def _hex32(value: Any, name: str, errors: list[str]) -> str | None:
    if not isinstance(value, str):
        errors.append(f"{name} must be a hex32 string")
        return None
    raw = value[2:] if value.startswith("0x") else value
    if len(raw) != 64:
        errors.append(f"{name} must be a hex32 string")
        return None
    try:
        bytes.fromhex(raw)
    except ValueError:
        errors.append(f"{name} must be a hex32 string")
        return None
    return raw.lower()


def _load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("packet", type=Path)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    report = validate_recursive_lifecycle_admission_packet_v1(_load_json(args.packet))
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
