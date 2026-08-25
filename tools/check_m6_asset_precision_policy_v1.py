#!/usr/bin/env python3
"""Fail closed if the governed M6 eight-decimal policy artifact drifts."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

if __package__:
    from src.core.global_economic_asset_precision_policy_v1 import (
        M6_ASSET_PRECISION_POLICY_ROOT_V1,
        m6_asset_precision_policy_canonical_v1,
    )
else:
    import sys

    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    from src.core.global_economic_asset_precision_policy_v1 import (
        M6_ASSET_PRECISION_POLICY_ROOT_V1,
        m6_asset_precision_policy_canonical_v1,
    )

REPO_ROOT = Path(__file__).resolve().parents[1]
POLICY_PATH = REPO_ROOT / "docs" / "research" / "ZENODEX_M6_ASSET_PRECISION_POLICY_V1.json"


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def check_m6_asset_precision_policy_v1(
    policy_path: Path = POLICY_PATH,
) -> dict[str, object]:
    findings: list[str] = []
    try:
        raw = json.loads(
            policy_path.read_text(encoding="utf-8"),
            object_pairs_hook=_reject_duplicate_keys,
        )
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as exc:
        raw = None
        findings.append(f"precision policy cannot be loaded: {type(exc).__name__}: {exc}")
    expected = m6_asset_precision_policy_canonical_v1()
    if type(raw) is not dict:
        if raw is not None:
            findings.append("precision policy must be an exact object")
    elif raw != expected:
        findings.append("precision policy content drift")
    return {
        "schema": "zenodex/m6-asset-precision-policy-check/v1",
        "ok": not findings,
        "findings": findings,
        "decimal_places": expected["decimal_places"],
        "atoms_per_display_unit": expected["atoms_per_display_unit"],
        "policy_root": M6_ASSET_PRECISION_POLICY_ROOT_V1,
        "production_authority": False,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--policy", type=Path, default=POLICY_PATH)
    args = parser.parse_args(argv)
    report = check_m6_asset_precision_policy_v1(args.policy)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
