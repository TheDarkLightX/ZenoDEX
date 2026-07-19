#!/usr/bin/env python3
"""Fail a release build if development/demo Python surfaces were packaged."""

from __future__ import annotations

import argparse
import ast
from pathlib import Path

FORBIDDEN_MODULES = frozenset(
    {
        "core/perp_np_clearinghouse.py",
        "core/perp_np_matching.py",
        "core/perp_np_matching_selftest.py",
        "core/perps_np_validation.py",
        "integration/autotrader_live_api.py",
        "integration/autotrader_live.py",
        "integration/confidential_attestation_api.py",
        "integration/dex_dispatch_proof_mining_reward.py",
        "integration/dex_dispatch_proof_mining_snapshots.py",
        "integration/dex_dispatch_proof_mining_templates.py",
        "integration/perps_api.py",
        "integration/tau_testnet_dex_plugin.py",
        "integration/tau_net_client.py",
        "integration/zeno_ledger_tokenomics.py",
        "integration/zenodex_local_signer.py",
        "integration/zusd_api.py",
    }
)

FORBIDDEN_PATHS = ("nonproduction",)

FORBIDDEN_IMPORT_PREFIXES = ("tools.zenodex_oracle_aggregate_adapter",)

FORBIDDEN_DEFINITIONS = frozenset(
    {
        "DEMO_SIGNER_PRIVKEY",
        "DexFaultInjectionConfig",
        "PERP_CHNP_MARKET_PREFIX",
        "PERP_OP_VERSION_CHNP_V1_2",
        "PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1",
        "PerpClearinghouseNpAccount",
        "PerpClearinghouseNpMarketState",
        "PerpClearinghouseNpPendingIntent",
        "StaticAutoTraderLanguageProvider",
        "SssBackupRecipient",
        "_InjectedFault",
        "_apply_chnp_op",
        "_apply_init_market_np",
        "_delivery_receipt_for_envelope",
        "_derive_coefficient",
        "_encrypt_share_envelope",
        "_eval_poly_gf256",
        "_fault_stage",
        "_local_fixture_delivery_receipt",
        "_load_nonproduction_np_core",
        "_register_for_test",
        "allow_nonproduction_np",
        "build_perps_wallet_encrypted_sss_recipient_keys_v1",
        "build_perps_wallet_encrypted_sss_backup_v1",
        "bls_pubkey_hex_from_privkey",
        "build_signed_tau_transaction",
        "createblock",
        "enable_test_fault_injection",
        "recipient_root_keys_from_fixture_v1",
        "send_signed_tx",
        "sign_dex_intent_for_engine",
        "sign_perp_op_for_engine",
        "sign_tau_transaction_payload",
        "split_secret_shamir_gf256",
    }
)

FORBIDDEN_SOURCE_FRAGMENTS = {
    "from ..nonproduction": "production import of non-production package",
    "from src.nonproduction": "production import of non-production package",
    "init_market_np": "retired fake-value perps action",
    "perp:chnp:": "retired fake-value perps market namespace",
    "/api/dex/build_settlement_spot_price_attestation": (
        "in-process settlement-attestation signing route"
    ),
    "/api/dex/proof_mining_payout_template": "local proof-mining payout-template route",
    "PERPS_WALLET_AUTO_MINE": "wallet API block-production switch",
    "PERPS_WALLET_ALLOW_LOCAL_SIGNING": "retired in-process wallet-signing switch",
    "PERPS_WALLET_RETURN_SIGNED_TAU_TX_PAYLOAD": "retired signed-payload disclosure switch",
    "ZUSD_TAU_WALLET_ALLOW_LOCAL_SIGNING": "retired in-process wallet-signing switch",
    "ZUSD_MONETARY_WALLET_ALLOW_LOCAL_SIGNING": "retired in-process wallet-signing switch",
    "ZUSD_MONETARY_WALLET_AUTO_MINE": "wallet API block-production switch",
    "ZUSD_TAU_WALLET_AUTO_MINE": "wallet API block-production switch",
}

RETIRED_SENTINEL_ONLY_FRAGMENTS = frozenset(
    {
        "PERPS_WALLET_AUTO_MINE",
        "PERPS_WALLET_ALLOW_LOCAL_SIGNING",
        "PERPS_WALLET_RETURN_SIGNED_TAU_TX_PAYLOAD",
        "ZUSD_TAU_WALLET_ALLOW_LOCAL_SIGNING",
        "ZUSD_MONETARY_WALLET_ALLOW_LOCAL_SIGNING",
        "ZUSD_MONETARY_WALLET_AUTO_MINE",
        "ZUSD_TAU_WALLET_AUTO_MINE",
    }
)


def violations(root: Path) -> list[str]:
    root = root.resolve()
    out: list[str] = []

    for relative in sorted(FORBIDDEN_MODULES):
        if (root / relative).is_file():
            out.append(f"forbidden production module: {relative}")

    for relative in FORBIDDEN_PATHS:
        if (root / relative).exists():
            out.append(f"forbidden production path: {relative}")

    for path in sorted(root.rglob("*")):
        if not path.is_file():
            continue
        relative = path.relative_to(root).as_posix()
        if "__pycache__" in path.parts or path.suffix in {".pyc", ".pyo"}:
            out.append(f"generated Python artifact: {relative}")
            continue
        if path.suffix != ".py":
            continue
        if path.name.startswith("zusd_multi"):
            out.append(f"incomplete multi-vault module: {relative}")
        try:
            source = path.read_text(encoding="utf-8")
            tree = ast.parse(source, filename=str(path))
        except (OSError, SyntaxError) as exc:
            out.append(f"uninspectable Python module: {relative}: {exc}")
            continue
        for fragment, label in FORBIDDEN_SOURCE_FRAGMENTS.items():
            if fragment in source and not (
                relative == "integration/api_server.py"
                and fragment in RETIRED_SENTINEL_ONLY_FRAGMENTS
            ):
                out.append(f"forbidden production source: {relative}:{label}")
        for node in ast.walk(tree):
            imported_modules: tuple[str, ...] = ()
            if isinstance(node, ast.ImportFrom) and node.module is not None:
                imported_modules = (
                    node.module,
                    *(f"{node.module}.{alias.name}" for alias in node.names),
                )
            elif isinstance(node, ast.Import):
                imported_modules = tuple(alias.name for alias in node.names)
            for imported_module in imported_modules:
                if any(
                    imported_module == prefix
                    or imported_module.startswith(prefix + ".")
                    for prefix in FORBIDDEN_IMPORT_PREFIXES
                ):
                    out.append(
                        "forbidden production import: "
                        f"{relative}:{getattr(node, 'lineno', 0)}:{imported_module}"
                    )
            name: str | None = None
            if isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
                name = node.name
            elif isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store):
                name = node.id
            if name in FORBIDDEN_DEFINITIONS:
                out.append(
                    f"forbidden production definition: {relative}:{getattr(node, 'lineno', 0)}:{name}"
                )

    return sorted(set(out))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    args = parser.parse_args()
    errors = violations(args.root)
    if errors:
        for error in errors:
            print(error)
        return 1
    print(f"production Python artifact accepted: {args.root}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
