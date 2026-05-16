#!/usr/bin/env python3
"""Check named DEX engine deployment profiles."""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from src.integration.deployment_profiles import (  # noqa: E402
    deployment_profile_ids,
    make_dex_engine_config_for_deployment_profile,
    validate_deployment_profile,
)

RESULT_SCHEMA = "zenodex.dex.deployment_profiles_check.v1"


def run_check() -> dict[str, object]:
    profiles: list[dict[str, object]] = []
    ok = True
    for profile_id in deployment_profile_ids():
        cfg = make_dex_engine_config_for_deployment_profile(profile_id)  # type: ignore[arg-type]
        accepted, error = validate_deployment_profile(profile_id, cfg)  # type: ignore[arg-type]
        ok = ok and accepted
        profiles.append(
            {
                "profile_id": profile_id,
                "status": "accepted" if accepted else "rejected",
                "error": error,
                "chain_id": cfg.chain_id,
                "require_intent_signatures": cfg.require_intent_signatures,
                "allow_unsigned_intents_if_tx_sender_matches": cfg.allow_unsigned_intents_if_tx_sender_matches,
                "require_all_nonces": cfg.dex_config.require_all_nonces,
                "settlement_validation": cfg.dex_config.settlement_validation,
                "require_uniform_batch_certificate": cfg.require_uniform_batch_certificate,
                "require_uniform_batch_price_grid_evidence": cfg.require_uniform_batch_price_grid_evidence,
                "require_oracle_authorization_for_protected_swaps": (
                    cfg.require_oracle_authorization_for_protected_swaps
                ),
                "require_oracle_authorization_for_critical_settlements": (
                    cfg.require_oracle_authorization_for_critical_settlements
                ),
            }
        )
    return {
        "schema": RESULT_SCHEMA,
        "ok": ok,
        "profiles": profiles,
    }


def main() -> int:
    result = run_check()
    print(json.dumps(result, sort_keys=True, indent=2))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
