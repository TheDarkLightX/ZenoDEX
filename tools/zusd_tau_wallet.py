#!/usr/bin/env python3
"""Wallet-facing CLI for Tau-native zUSD transfers.

Collateralized minting, repayment, redemption, and protocol burns use the zUSD
monetary command surface.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zusd_tau_token import (  # noqa: E402
    ZUSDTauTokenConfig,
    ZUSDTauTokenReport,
    derive_zusd_tau_asset_id,
    prepare_zusd_tau_token_operation,
    require_zusd_tau_transport_action,
)


def _emit_json(data: dict[str, Any], *, pretty: bool) -> None:
    print(json.dumps(data, indent=2 if pretty else None, sort_keys=True))


def _report_to_dict(report: ZUSDTauTokenReport) -> dict[str, Any]:
    return {
        "schema": "zenodex/zusd-tau-token-report/v1",
        "action": report.action,
        "asset_id": report.asset_id,
        "nonce_key": report.nonce_key,
        "nonce_before": int(report.nonce_before),
        "nonce_after": int(report.nonce_after),
        "operation": dict(report.operation),
        "operations": dict(report.operations),
        "sender_balance_after": int(report.sender_balance_after),
        "recipient_balance_after": int(report.recipient_balance_after),
        "supply_after": int(report.supply_after),
        "tau_receipts": [
            {
                "spec_id": receipt.spec_id,
                "gate_output": receipt.gate_output,
                "steps": [dict(step) for step in receipt.steps],
                "expected_ok": bool(receipt.expected_ok),
            }
            for receipt in report.tau_receipts
        ],
        "tau_tx_payload": report.tau_tx_payload,
    }


def _add_common_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--amount", required=True, type=int)
    parser.add_argument("--deadline", required=True, type=int)
    parser.add_argument("--last-used-nonce", required=True, type=int)
    parser.add_argument("--total-supply-before", required=True, type=int)
    parser.add_argument("--asset-id")
    parser.add_argument("--chain-id", default="tau-net-alpha")
    parser.add_argument("--tau-enabled", action="store_true")
    parser.add_argument("--tau-bin")
    parser.add_argument("--tau-timeout-s", type=float, default=2.0)
    parser.add_argument("--tau-allow-path-lookup", action="store_true")
    parser.add_argument("--signer-privkey")
    parser.add_argument("--tx-sequence-number", type=int)
    parser.add_argument("--tx-expiration-time", type=int)
    parser.add_argument("--tx-fee-limit", default="0")
    parser.add_argument("--telemetry-out")
    parser.add_argument("--pretty", action="store_true")


def main(argv: list[str] | None = None) -> int:
    raw_argv = list(sys.argv[1:] if argv is None else argv)
    if raw_argv and raw_argv[0] in {"mint", "burn"}:
        try:
            require_zusd_tau_transport_action(
                action=raw_argv[0],
                asset_id=derive_zusd_tau_asset_id(),
            )
        except ValueError as exc:
            print(
                json.dumps(
                    {
                        "ok": False,
                        "error": f"ValueError: {exc}",
                        "derived_asset_id": None,
                    },
                    sort_keys=True,
                ),
                file=sys.stderr,
            )
            return 1
        raise RuntimeError("managed zUSD supply command unexpectedly passed policy")

    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True, metavar="{transfer}")

    transfer = sub.add_parser("transfer")
    _add_common_args(transfer)
    transfer.add_argument("--sender-pubkey", required=True)
    transfer.add_argument("--recipient-pubkey", required=True)
    transfer.add_argument("--sender-balance-before", required=True, type=int)
    transfer.add_argument("--recipient-balance-before", required=True, type=int)
    transfer.add_argument("--paused", action="store_true")
    transfer.add_argument("--auth-ok", action=argparse.BooleanOptionalAction, default=True)

    args = parser.parse_args(raw_argv)
    try:
        tau_config = ZUSDTauTokenConfig(
            enabled=bool(args.tau_enabled),
            timeout_s=float(args.tau_timeout_s),
            tau_bin=(args.tau_bin or None),
            allow_path_lookup=bool(args.tau_allow_path_lookup),
        )
        report = prepare_zusd_tau_token_operation(
            action=args.action,
            amount=int(args.amount),
            deadline=int(args.deadline),
            last_used_nonce=int(args.last_used_nonce),
            total_supply_before=int(args.total_supply_before),
            sender_balance_before=int(getattr(args, "sender_balance_before", 0)),
            recipient_balance_before=int(getattr(args, "recipient_balance_before", 0)),
            sender_pubkey=getattr(args, "sender_pubkey", None),
            recipient_pubkey=getattr(args, "recipient_pubkey", None),
            operator_pubkey=getattr(args, "operator_pubkey", None),
            paused=bool(getattr(args, "paused", False)),
            auth_ok=bool(getattr(args, "auth_ok", True)),
            asset_id=args.asset_id,
            chain_id=str(args.chain_id),
            tau_config=tau_config,
            signer_privkey=args.signer_privkey,
            tx_sequence_number=args.tx_sequence_number,
            tx_expiration_time=args.tx_expiration_time,
            tx_fee_limit=args.tx_fee_limit,
        )
        payload = _report_to_dict(report)
        if args.telemetry_out:
            Path(args.telemetry_out).write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
        _emit_json(payload, pretty=bool(args.pretty))
        return 0
    except Exception as exc:
        payload = {
            "ok": False,
            "error": f"{type(exc).__name__}: {exc}",
            "derived_asset_id": None if args.asset_id else derive_zusd_tau_asset_id(chain_id=str(args.chain_id)),
        }
        if args.telemetry_out:
            Path(args.telemetry_out).write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
        print(json.dumps(payload, sort_keys=True), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
