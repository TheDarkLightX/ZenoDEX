#!/usr/bin/env python3
"""Validate the runtime UI configuration before production services start."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
from typing import Any, Mapping

FORBIDDEN_CAPABILITY_KEYS = frozenset(
    {"demoMode", "allowDemoMode", "allowBrowserKeyGeneration"}
)
EXPECTED_UI_CONTRACT_SCHEMA = "zenodex.dex_ui.surface_contract.v1"
EXPECTED_UI_CONTRACT_VERSION = "dex-ui-production-facing-20260719-v7"
EXPECTED_UI_CONTRACT_HASH = (
    "sha256:2721e6bf0c44c9038f76d281d1110e41b14e437ec5da98f0941764ff564ed7f7"
)


def validation_errors(config: object, *, expected_chain_id: str) -> tuple[str, ...]:
    errors: list[str] = []
    if type(config) is not dict:
        return ("config_root_must_be_object",)
    obj: Mapping[str, Any] = config

    if type(expected_chain_id) is not str or not expected_chain_id:
        errors.append("expected_chain_id_must_be_nonempty")
    if obj.get("deployment") != "production":
        errors.append("deployment_must_be_production")
    if obj.get("chainId") != expected_chain_id:
        errors.append("chain_id_mismatch")
    for key in sorted(FORBIDDEN_CAPABILITY_KEYS):
        if key in obj:
            errors.append(f"forbidden_capability_key:{key}")
    if obj.get("allowDefaultExternalSigner") is not False:
        errors.append("default_external_signer_must_be_disabled")

    for key in ("apiBase", "zenoOracleApiBase"):
        if key not in obj:
            errors.append(f"{key}_must_be_explicit")
        elif type(obj[key]) is not str:
            errors.append(f"{key}_must_be_string")

    expected_contract_binding = {
        "uiSurfaceContractSchema": EXPECTED_UI_CONTRACT_SCHEMA,
        "uiSurfaceContractVersion": EXPECTED_UI_CONTRACT_VERSION,
        "uiSurfaceContractHash": EXPECTED_UI_CONTRACT_HASH,
    }
    for key, expected in expected_contract_binding.items():
        if obj.get(key) != expected:
            errors.append(f"{key}_mismatch")

    return tuple(errors)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "path",
        nargs="?",
        type=Path,
        default=Path("/var/www/zenodex/zenodex-config.json"),
    )
    parser.add_argument(
        "--expected-chain-id",
        default=os.environ.get("TAU_DEX_CHAIN_ID", ""),
    )
    args = parser.parse_args()
    try:
        config = json.loads(args.path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        print(f"invalid production UI runtime config: {exc}")
        return 1
    errors = validation_errors(config, expected_chain_id=args.expected_chain_id)
    if errors:
        for error in errors:
            print(error)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
