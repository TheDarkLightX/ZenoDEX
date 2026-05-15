#!/usr/bin/env python3
"""Verify a ZenoLedger v0 header/body sequence."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_profile import (  # noqa: E402
    validate_checkpoint_admission_v0,
    validate_zeno_ledger_profile_v0,
)
from src.integration.zeno_ledger_v0 import (
    canonical_header_hash_v0,
    validate_checkpoint_header_binding_v0,
    validate_header_body_roots_v0,
    validate_header_v0,
)

ZERO_ROOT = "0x" + "00" * 32
REPORT_SCHEMA = "zenodex.zeno_ledger.verify_report.v0"


def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def verify_zeno_ledger_v0(
    *,
    headers_dir: Path,
    bodies_dir: Path,
    checkpoints_dir: Path | None,
    profile_path: Path | None,
    from_height: int,
    to_height: int,
    trusted_prev_header_hash: str = ZERO_ROOT,
) -> dict[str, Any]:
    errors: list[str] = []
    checked_heights: list[int] = []
    last_header_hash: str | None = None
    last_post_state_root: str | None = None
    last_app_hash: str | None = None
    expected_prev_hash = trusted_prev_header_hash

    if from_height < 0:
        errors.append("from_height_must_be_nonnegative")
    if to_height < from_height:
        errors.append("to_height_before_from_height")
    if not headers_dir.is_dir():
        errors.append("headers_dir_missing")
    if not bodies_dir.is_dir():
        errors.append("bodies_dir_missing")
    profile: dict[str, Any] | None = None
    if profile_path is not None:
        if checkpoints_dir is None:
            errors.append("profile_requires_checkpoints_dir")
        elif not profile_path.is_file():
            errors.append("profile_missing")
        else:
            try:
                profile = dict(_load_json_object(profile_path))
                validate_zeno_ledger_profile_v0(profile)
            except Exception as exc:
                errors.append(f"profile_invalid:{exc}")
    if errors:
        return _report(
            errors=errors,
            checked_heights=checked_heights,
            last_header_hash=last_header_hash,
            last_post_state_root=last_post_state_root,
            last_app_hash=last_app_hash,
        )

    for height in range(from_height, to_height + 1):
        header_path = headers_dir / f"{height}.json"
        body_path = bodies_dir / f"{height}.json"
        if not header_path.is_file():
            errors.append(f"header_missing:{height}")
            break
        if not body_path.is_file():
            errors.append(f"body_missing:{height}")
            break

        try:
            header = dict(_load_json_object(header_path))
            body = dict(_load_json_object(body_path))
            validate_header_v0(header)
            if header["height"] != height:
                raise ValueError(f"header height mismatch for file {height}")
            if header["prev_header_hash"] != expected_prev_hash:
                raise ValueError(f"prev_header_hash mismatch at height {height}")
            validate_header_body_roots_v0(header, body)
            if checkpoints_dir is not None:
                checkpoint_path = checkpoints_dir / f"{height}.json"
                if not checkpoint_path.is_file():
                    raise ValueError(f"checkpoint missing at height {height}")
                checkpoint = dict(_load_json_object(checkpoint_path))
                validate_checkpoint_header_binding_v0(checkpoint, header)
                if profile is not None:
                    validate_checkpoint_admission_v0(checkpoint=checkpoint, profile=profile)
            last_header_hash = canonical_header_hash_v0(header)
            last_post_state_root = str(header["post_state_root"])
            last_app_hash = str(header["app_hash"])
            expected_prev_hash = last_header_hash
            checked_heights.append(height)
        except Exception as exc:
            errors.append(f"height_{height}_invalid:{exc}")
            break

    return _report(
        errors=errors,
        checked_heights=checked_heights,
        last_header_hash=last_header_hash,
        last_post_state_root=last_post_state_root,
        last_app_hash=last_app_hash,
    )


def _report(
    *,
    errors: list[str],
    checked_heights: list[int],
    last_header_hash: str | None,
    last_post_state_root: str | None,
    last_app_hash: str | None,
) -> dict[str, Any]:
    ok = not errors
    return {
        "schema": REPORT_SCHEMA,
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "checked_heights": checked_heights,
        "last_header_hash": last_header_hash,
        "last_post_state_root": last_post_state_root,
        "last_app_hash": last_app_hash,
        "errors": errors,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Verify a ZenoLedger v0 header/body sequence")
    parser.add_argument("--headers-dir", required=True, type=Path)
    parser.add_argument("--bodies-dir", required=True, type=Path)
    parser.add_argument("--checkpoints-dir", type=Path)
    parser.add_argument("--profile", type=Path)
    parser.add_argument("--from-height", required=True, type=int)
    parser.add_argument("--to-height", required=True, type=int)
    parser.add_argument("--trusted-prev-header-hash", default=ZERO_ROOT)
    args = parser.parse_args(argv)

    result = verify_zeno_ledger_v0(
        headers_dir=args.headers_dir,
        bodies_dir=args.bodies_dir,
        checkpoints_dir=args.checkpoints_dir,
        profile_path=args.profile,
        from_height=args.from_height,
        to_height=args.to_height,
        trusted_prev_header_hash=args.trusted_prev_header_hash,
    )
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
