#!/usr/bin/env python3
"""Check API surface profile postures."""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from src.integration.api_surface_profiles import (  # noqa: E402
    API_SURFACE_PROFILE_LOCAL_DEMO,
    API_SURFACE_PROFILE_PRODUCTION_STRICT,
    API_SURFACE_PROFILE_PUBLIC_TESTNET,
    api_surface_profile_ids,
    validate_api_surface_profile,
)

RESULT_SCHEMA = "zenodex.api.surface_profiles_check.v1"


def run_check() -> dict[str, object]:
    cases = [
        {
            "name": "local_demo_accepts_dex_without_token",
            "profile_id": API_SURFACE_PROFILE_LOCAL_DEMO,
            "demo_api_token": "",
            "perps_enabled": False,
            "zusd_enabled": False,
            "dex_enabled": True,
            "expect_ok": True,
        },
        {
            "name": "public_testnet_requires_token",
            "profile_id": API_SURFACE_PROFILE_PUBLIC_TESTNET,
            "demo_api_token": "",
            "perps_enabled": False,
            "zusd_enabled": False,
            "dex_enabled": True,
            "expect_ok": False,
        },
        {
            "name": "public_testnet_accepts_token",
            "profile_id": API_SURFACE_PROFILE_PUBLIC_TESTNET,
            "demo_api_token": "configured",
            "perps_enabled": False,
            "zusd_enabled": False,
            "dex_enabled": True,
            "expect_ok": True,
        },
        {
            "name": "production_strict_forbids_demo_routes",
            "profile_id": API_SURFACE_PROFILE_PRODUCTION_STRICT,
            "demo_api_token": "configured",
            "perps_enabled": True,
            "zusd_enabled": False,
            "dex_enabled": False,
            "confidential_enabled": False,
            "expect_ok": False,
        },
        {
            "name": "production_strict_forbids_confidential_routes",
            "profile_id": API_SURFACE_PROFILE_PRODUCTION_STRICT,
            "demo_api_token": "configured",
            "perps_enabled": False,
            "zusd_enabled": False,
            "dex_enabled": False,
            "confidential_enabled": True,
            "expect_ok": False,
        },
        {
            "name": "production_strict_accepts_health_only",
            "profile_id": API_SURFACE_PROFILE_PRODUCTION_STRICT,
            "demo_api_token": "",
            "perps_enabled": False,
            "zusd_enabled": False,
            "dex_enabled": False,
            "expect_ok": True,
        },
    ]
    results: list[dict[str, object]] = []
    ok = True
    for case in cases:
        accepted, error = validate_api_surface_profile(
            profile_id=str(case["profile_id"]),
            demo_api_token=str(case["demo_api_token"]),
            perps_enabled=bool(case["perps_enabled"]),
            zusd_enabled=bool(case["zusd_enabled"]),
            dex_enabled=bool(case["dex_enabled"]),
            confidential_enabled=bool(case.get("confidential_enabled", False)),
        )
        case_ok = accepted is bool(case["expect_ok"])
        ok = ok and case_ok
        results.append(
            {
                "name": case["name"],
                "status": "accepted" if accepted else "rejected",
                "expected_status": "accepted" if case["expect_ok"] else "rejected",
                "ok": case_ok,
                "error": error,
            }
        )
    return {
        "schema": RESULT_SCHEMA,
        "ok": ok,
        "profile_ids": api_surface_profile_ids(),
        "cases": results,
    }


def check_api_surface_profiles(root: Path = ROOT) -> dict[str, object]:
    _ = root
    return run_check()


def main() -> int:
    result = run_check()
    print(json.dumps(result, sort_keys=True, indent=2))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
