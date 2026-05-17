#!/usr/bin/env python3
"""Validate a bounded ZenoCover reserve-solvency manifest."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.check_zenocover_lp_loss_cover import validate_zenocover_lp_loss_cover_bundle  # noqa: E402

MANIFEST_SCHEMA = "zenodex.zenocover.reserve_solvency_manifest.v0"
REPORT_SCHEMA = "zenodex.zenocover.reserve_solvency_report.v0"
COUNTED_STATUSES = {"active"}
ALLOWED_STATUSES = {"active", "expired", "settled"}


def validate_zenocover_reserve_solvency_v0(
    manifest: Any,
    *,
    base_dir: str | Path = ROOT,
) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(manifest, "manifest", errors)
    if obj.get("schema") != MANIFEST_SCHEMA:
        errors.append("schema mismatch")

    reserve = _mapping(obj.get("reserve"), "reserve", errors)
    reserve_asset = _str(reserve.get("asset"), "reserve.asset", errors)
    reserve_balance = _int_ge(reserve.get("balance"), "reserve.balance", errors, 0)
    existing_locked = _int_ge(reserve.get("existing_locked"), "reserve.existing_locked", errors, 0)
    min_surplus = _int_ge(reserve.get("min_surplus"), "reserve.min_surplus", errors, 0)

    positions_raw = obj.get("positions")
    if not isinstance(positions_raw, list):
        errors.append("positions must be a list")
        positions_raw = []

    seen_ids: set[str] = set()
    position_reports: list[dict[str, Any]] = []
    active_required = 0
    for index, item in enumerate(positions_raw):
        position_errors: list[str] = []
        position = _mapping(item, f"positions[{index}]", position_errors)
        position_id = _str(position.get("id"), f"positions[{index}].id", position_errors)
        status = _str(position.get("status"), f"positions[{index}].status", position_errors)
        bundle_dir_raw = _str(position.get("bundle_dir"), f"positions[{index}].bundle_dir", position_errors)
        expected_bundle_hash = _optional_str(
            position.get("expected_bundle_hash"),
            f"positions[{index}].expected_bundle_hash",
            position_errors,
        )
        expected_bundle_file_sha256 = _optional_str(
            position.get("expected_bundle_file_sha256"),
            f"positions[{index}].expected_bundle_file_sha256",
            position_errors,
        )
        if position_id is not None:
            if position_id in seen_ids:
                position_errors.append("position id must be unique")
            seen_ids.add(position_id)
        if status is not None and status not in ALLOWED_STATUSES:
            position_errors.append("position status is unsupported")

        bundle_report: dict[str, Any] | None = None
        required_collateral = None
        if bundle_dir_raw is not None:
            bundle_dir = _resolve_bundle_dir(bundle_dir_raw, base_dir=Path(base_dir))
            bundle_report = validate_zenocover_lp_loss_cover_bundle(
                bundle_dir,
                expected_bundle_hash=expected_bundle_hash,
                expected_bundle_file_sha256=expected_bundle_file_sha256,
            )
            if bundle_report.get("ok") is not True:
                position_errors.append("bundle replay rejected")
            else:
                settlement = _mapping(bundle_report.get("settlement"), "bundle_report.settlement", position_errors)
                required_collateral = _int_ge(
                    settlement.get("writer_collateral_required"),
                    "bundle_report.settlement.writer_collateral_required",
                    position_errors,
                    0,
                )
                writer_posted = _int_ge(
                    settlement.get("writer_posted"),
                    "bundle_report.settlement.writer_posted",
                    position_errors,
                    0,
                )
                if (
                    required_collateral is not None
                    and writer_posted is not None
                    and writer_posted < required_collateral
                ):
                    position_errors.append("writer_posted below writer_collateral_required")

        if status in COUNTED_STATUSES and required_collateral is not None:
            active_required += required_collateral

        position_reports.append(
            {
                "id": position_id,
                "status": status,
                "ok": not position_errors,
                "errors": position_errors,
                "required_collateral": required_collateral,
                "bundle_hash": None if bundle_report is None else bundle_report.get("bundle_hash"),
                "bundle_errors": [] if bundle_report is None else list(bundle_report.get("errors", [])),
            }
        )

    surplus_after_active = None
    if None not in (reserve_balance, existing_locked, min_surplus):
        surplus_after_active = int(reserve_balance) - int(existing_locked) - active_required
        if surplus_after_active < int(min_surplus):
            errors.append("reserve balance below active collateral plus min_surplus")
    if any(not report["ok"] for report in position_reports):
        errors.append("one or more positions rejected")

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "facts": {
            "reserve_asset": reserve_asset,
            "reserve_balance": reserve_balance,
            "existing_locked": existing_locked,
            "active_required_collateral": active_required,
            "min_surplus": min_surplus,
            "surplus_after_active": surplus_after_active,
            "position_count": len(position_reports),
        },
        "positions": position_reports,
    }


def _resolve_bundle_dir(raw: str, *, base_dir: Path) -> Path:
    path = Path(raw)
    if path.is_absolute():
        return path
    return base_dir / path


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        errors.append(f"{name} must be an object")
        return {}
    return value


def _str(value: Any, name: str, errors: list[str]) -> str | None:
    if not isinstance(value, str) or value == "":
        errors.append(f"{name} must be a non-empty string")
        return None
    return value


def _optional_str(value: Any, name: str, errors: list[str]) -> str | None:
    if value is None:
        return None
    return _str(value, name, errors)


def _int_ge(value: Any, name: str, errors: list[str], minimum: int) -> int | None:
    if not isinstance(value, int) or isinstance(value, bool):
        errors.append(f"{name} must be an int")
        return None
    if value < minimum:
        errors.append(f"{name} must be >= {minimum}")
        return None
    return int(value)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--base-dir", type=Path, default=ROOT)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    report = validate_zenocover_reserve_solvency_v0(manifest, base_dir=args.base_dir)
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
