#!/usr/bin/env python3
"""Verify an attested confidential route-quote bundle."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.confidential_extension_receipts import (  # noqa: E402
    confidential_measurement_registry_approves_receipt,
    confidential_measurement_registry_hash,
    verify_confidential_extension_receipt,
    verify_confidential_measurement_registry,
)
from src.core.quote_receipts import receipt_hash, verify_route_quote_receipt  # noqa: E402
from src.state.pools import PoolState, PoolStatus  # noqa: E402

BUNDLE_SCHEMA = "zenodex.confidential_route_quote_bundle.v0"
REPORT_SCHEMA = "zenodex.confidential_route_quote_bundle_report.v0"
DEFAULT_EXTENSION_ID = "private-route-quote-v1"
REQUEST_BINDING_PREFIX = "quote_receipt:"


def validate_confidential_route_quote_bundle_v0(bundle: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(bundle, "bundle", errors)
    if obj.get("schema") != BUNDLE_SCHEMA:
        errors.append("schema mismatch")

    tee_receipt = _mapping(obj.get("tee_receipt"), "tee_receipt", errors)
    quote_receipt = _mapping(obj.get("quote_receipt"), "quote_receipt", errors)
    pools_raw = _mapping(obj.get("pools"), "pools", errors)
    expected_extension_id = _str(obj.get("expected_extension_id"), "expected_extension_id", errors)
    if expected_extension_id is not None and expected_extension_id != DEFAULT_EXTENSION_ID:
        errors.append(f"expected_extension_id must be {DEFAULT_EXTENSION_ID}")
    max_quote_age = _nonnegative_int(obj.get("max_quote_age"), "max_quote_age", errors)

    receipt_body = _mapping(tee_receipt.get("body"), "tee_receipt.body", errors)
    attestation = _mapping(receipt_body.get("attestation"), "tee_receipt.body.attestation", errors)
    host = _mapping(receipt_body.get("host"), "tee_receipt.body.host", errors)
    current_epoch = _nonnegative_int(attestation.get("current_epoch"), "current_epoch", errors)
    policy_digest = _str(receipt_body.get("policy_digest"), "policy_digest", errors)

    approved_measurements: set[str] = set()
    measurement_registry_hash: str | None = None
    registry_obj = obj.get("measurement_registry")
    if isinstance(registry_obj, Mapping):
        if current_epoch is None or policy_digest is None:
            errors.append("measurement registry requires current_epoch and policy_digest")
        else:
            registry_ok, registry_err, active = verify_confidential_measurement_registry(
                dict(registry_obj),
                current_epoch=current_epoch,
                policy_digest=policy_digest,
            )
            if not registry_ok:
                errors.append(f"measurement registry rejected: {registry_err}")
            approved_measurements = set(active)
            measurement_registry_hash = confidential_measurement_registry_hash(dict(registry_obj))
            provider_id = _str(receipt_body.get("provider_id"), "provider_id", errors)
            measurement = _str(receipt_body.get("measurement"), "measurement", errors)
            if registry_ok and provider_id is not None and measurement is not None:
                provider_ok, provider_err = confidential_measurement_registry_approves_receipt(
                    dict(registry_obj),
                    provider_id=provider_id,
                    measurement=measurement,
                    current_epoch=current_epoch,
                    policy_digest=policy_digest,
                )
                if not provider_ok:
                    if measurement not in approved_measurements:
                        errors.append("receipt measurement is not active in measurement_registry")
                    else:
                        errors.append(
                            "receipt measurement/provider is not active in measurement_registry: "
                            f"{provider_err}"
                        )
    else:
        approved = obj.get("approved_measurements")
        if not isinstance(approved, list) or not all(isinstance(item, str) and item for item in approved):
            errors.append("approved_measurements must be a non-empty string list when registry is absent")
        else:
            approved_measurements = set(approved)

    tee_ok = False
    tee_err = "not_checked"
    if not errors:
        tee_ok, tee_err = verify_confidential_extension_receipt(
            dict(tee_receipt),
            approved_measurements=approved_measurements,
        )
        if not tee_ok:
            errors.append(f"tee receipt rejected: {tee_err}")

    quote_hash = None
    if isinstance(quote_receipt.get("body"), Mapping):
        quote_hash = receipt_hash(dict(quote_receipt["body"]))
    supplied_quote_hash = quote_receipt.get("receipt_hash")
    if not isinstance(supplied_quote_hash, str) or not supplied_quote_hash:
        errors.append("quote_receipt.receipt_hash must be a non-empty string")
    elif quote_hash is not None and quote_hash != supplied_quote_hash:
        errors.append("quote receipt hash mismatch")

    request_id = receipt_body.get("request_id")
    if isinstance(supplied_quote_hash, str):
        expected_request_id = f"{REQUEST_BINDING_PREFIX}{supplied_quote_hash}"
        if request_id != expected_request_id:
            errors.append("TEE request_id must bind quote receipt hash")

    extension_ok = receipt_body.get("extension_id") == DEFAULT_EXTENSION_ID
    if receipt_body.get("extension_id") != DEFAULT_EXTENSION_ID:
        errors.append(f"TEE extension_id must be {DEFAULT_EXTENSION_ID}")
    do_execute = _binary_int(host.get("do_execute"), "TEE host.do_execute", errors)
    policy_ok = _binary_int(host.get("policy_ok"), "TEE host.policy_ok", errors)
    nonce_unused = _binary_int(host.get("nonce_unused"), "TEE host.nonce_unused", errors)
    output_bound_ok = _binary_int(host.get("output_bound_ok"), "TEE host.output_bound_ok", errors)
    host_guards_ok = do_execute == 1 and policy_ok == 1 and nonce_unused == 1 and output_bound_ok == 1
    if do_execute is not None and do_execute != 1:
        errors.append("TEE host.do_execute must be 1 for quote output admission")
    if (
        (policy_ok is not None and policy_ok != 1)
        or (nonce_unused is not None and nonce_unused != 1)
        or (output_bound_ok is not None and output_bound_ok != 1)
    ):
        errors.append("TEE host guards must all be 1 for quote output admission")

    quote_epoch = None
    quote_body = quote_receipt.get("body")
    if isinstance(quote_body, Mapping):
        quote_epoch = _nonnegative_int(quote_body.get("quote_epoch"), "quote_receipt.body.quote_epoch", errors)
    else:
        errors.append("quote_receipt.body must be an object")
    if current_epoch is not None and quote_epoch is not None and max_quote_age is not None:
        if quote_epoch > current_epoch:
            errors.append("quote epoch must not be in the future")
        elif current_epoch - quote_epoch > max_quote_age:
            errors.append("quote epoch exceeds max_quote_age")

    privacy_evidence = {
        "measurement_approval": bool(approved_measurements),
        "measurement_registry_checked": isinstance(registry_obj, Mapping),
        "extension_id_bound": extension_ok,
        "request_id_binds_quote_receipt": (
            isinstance(supplied_quote_hash, str)
            and request_id == f"{REQUEST_BINDING_PREFIX}{supplied_quote_hash}"
        ),
        "host_guards_ok": host_guards_ok,
        "quote_epoch_fresh": (
            current_epoch is not None
            and quote_epoch is not None
            and max_quote_age is not None
            and quote_epoch <= current_epoch
            and current_epoch - quote_epoch <= max_quote_age
        ),
    }

    pools_by_id: dict[str, PoolState] = {}
    if not errors:
        try:
            pools_by_id = _pool_map_from_manifest(pools_raw)
        except ValueError as exc:
            errors.append(str(exc))

    quote_ok = False
    quote_err = "not_checked"
    if not errors and quote_epoch is not None:
        quote_ok, quote_err = verify_route_quote_receipt(
            dict(quote_receipt),
            pools_by_id=pools_by_id,
            expected_quote_epoch=quote_epoch,
        )
        if not quote_ok:
            errors.append(f"quote receipt rejected: {quote_err}")

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "tee_verified": tee_ok,
        "tee_error": tee_err,
        "quote_verified": quote_ok,
        "quote_error": quote_err,
        "quote_receipt_hash": supplied_quote_hash if isinstance(supplied_quote_hash, str) else None,
        "measurement_registry_hash": measurement_registry_hash,
        "privacy_evidence": privacy_evidence,
        "pool_count": len(pools_by_id),
        "current_epoch": current_epoch,
        "quote_epoch": quote_epoch,
    }


def _pool_map_from_manifest(pools: Mapping[str, Any]) -> dict[str, PoolState]:
    out: dict[str, PoolState] = {}
    for pool_id, raw in pools.items():
        if not isinstance(pool_id, str) or not pool_id:
            raise ValueError("pool ids must be non-empty strings")
        if not isinstance(raw, Mapping):
            raise ValueError("pool entries must be objects")
        status_raw = raw.get("status")
        if not isinstance(status_raw, str):
            raise ValueError("pool status must be a string")
        try:
            status = PoolStatus(status_raw)
        except ValueError as exc:
            raise ValueError("pool status is unsupported") from exc
        pool = PoolState(
            pool_id=pool_id,
            asset0=_required_str(raw.get("asset0"), "pool.asset0"),
            asset1=_required_str(raw.get("asset1"), "pool.asset1"),
            reserve0=_required_int(raw.get("reserve0"), "pool.reserve0"),
            reserve1=_required_int(raw.get("reserve1"), "pool.reserve1"),
            fee_bps=_required_int(raw.get("fee_bps"), "pool.fee_bps"),
            lp_supply=_required_int(raw.get("lp_supply"), "pool.lp_supply"),
            status=status,
            created_at=_required_int(raw.get("created_at"), "pool.created_at"),
            curve_tag=str(raw.get("curve_tag", "CPMM")),
            curve_params=str(raw.get("curve_params", "")),
        )
        out[pool_id] = pool
    if not out:
        raise ValueError("pools must be non-empty")
    return out


def _required_str(value: Any, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _required_int(value: Any, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{name} must be an int")
    return value


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if isinstance(value, Mapping):
        return value
    errors.append(f"{name} must be an object")
    return {}


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


def _binary_int(value: Any, name: str, errors: list[str]) -> int | None:
    if isinstance(value, int) and not isinstance(value, bool) and value in (0, 1):
        return value
    errors.append(f"{name} must be a 0/1 int")
    return None


def _load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("bundle", type=Path)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    report = validate_confidential_route_quote_bundle_v0(_load_json(args.bundle))
    print(json.dumps(report, sort_keys=True, indent=2 if args.pretty else None))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
