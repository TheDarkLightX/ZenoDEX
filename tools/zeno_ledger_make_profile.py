#!/usr/bin/env python3
"""Build a ZenoLedger v0 admission profile."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_profile import (
    DEPLOYMENT_MODE_LOCAL_SANDBOX_V0,
    DEPLOYMENT_MODE_TAU_EXCLUSIVE_RELEASE_V0,
    DEPLOYMENT_MODE_ZENO_SOVEREIGN_TESTNET_V0,
)
from tools.support.zeno_ledger_profile_samples import (  # noqa: E402
    sample_local_sandbox_profile_v0,
    sample_tau_exclusive_release_profile_v0,
    sample_zeno_sovereign_testnet_profile_v0,
)

REPORT_SCHEMA = "zenodex.zeno_ledger.make_profile_report.v0"


def build_profile_from_args(args: argparse.Namespace) -> dict[str, object]:
    if args.mode == DEPLOYMENT_MODE_LOCAL_SANDBOX_V0:
        return sample_local_sandbox_profile_v0(
            chain_id=args.chain_id,
            config_digest=args.config_digest,
            sequencer_set_hash=args.sequencer_set_hash,
        )
    if args.mode == DEPLOYMENT_MODE_ZENO_SOVEREIGN_TESTNET_V0:
        return sample_zeno_sovereign_testnet_profile_v0(
            chain_id=args.chain_id,
            config_digest=args.config_digest,
            sequencer_set_hash=args.sequencer_set_hash,
            token_symbol=args.token_symbol,
            token_asset_id=args.token_asset_id,
            proof_required=bool(args.proof_required),
        )
    if args.mode == DEPLOYMENT_MODE_TAU_EXCLUSIVE_RELEASE_V0:
        return sample_tau_exclusive_release_profile_v0(
            chain_id=args.chain_id,
            config_digest=args.config_digest,
            sequencer_set_hash=args.sequencer_set_hash,
            token_symbol=args.token_symbol,
            token_asset_id=args.token_asset_id,
        )
    raise ValueError(f"unsupported mode: {args.mode}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build a ZenoLedger v0 admission profile")
    parser.add_argument(
        "--mode",
        required=True,
        choices=[
            DEPLOYMENT_MODE_LOCAL_SANDBOX_V0,
            DEPLOYMENT_MODE_ZENO_SOVEREIGN_TESTNET_V0,
            DEPLOYMENT_MODE_TAU_EXCLUSIVE_RELEASE_V0,
        ],
    )
    parser.add_argument("--chain-id", required=True)
    parser.add_argument("--config-digest", required=True)
    parser.add_argument("--sequencer-set-hash", required=True)
    parser.add_argument("--token-symbol", default="")
    parser.add_argument("--token-asset-id", default="0x" + "00" * 32)
    parser.add_argument("--proof-required", action="store_true")
    parser.add_argument("--out", type=Path)
    args = parser.parse_args(argv)

    try:
        profile = build_profile_from_args(args)
        if args.out is not None:
            args.out.parent.mkdir(parents=True, exist_ok=True)
            args.out.write_text(json.dumps(profile, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        report = {
            "schema": REPORT_SCHEMA,
            "ok": True,
            "status": "accepted",
            "profile": profile,
        }
        if args.out is not None:
            report["profile_path"] = str(args.out)
    except Exception as exc:
        report = {
            "schema": REPORT_SCHEMA,
            "ok": False,
            "status": "rejected",
            "errors": [str(exc)],
        }
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
