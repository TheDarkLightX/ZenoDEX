#!/usr/bin/env python3
# ruff: noqa: E402
"""Build a deterministic sovereign ZenoLedger testnet bootstrap bundle."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.dex import DexState
from src.integration.dex_engine import DexEngineConfig
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.zeno_ledger_profile import sample_zeno_sovereign_testnet_profile_v0
from src.integration.zeno_ledger_replay import (
    replay_engine_config_digest_v0,
    replay_engine_config_document_v0,
)
from src.integration.zeno_ledger_tokenomics import (
    DEFAULT_PROTOCOL_TOKEN_SYMBOL,
    build_protocol_token_distribution_v0,
    load_role_pubkeys_from_key_bundle_v0,
    validate_protocol_token_distribution_v0,
)
from src.integration.zeno_ledger_v0 import (
    BATCH_CUTOFF_SCHEMA_V0,
    BODY_SCHEMA_V0,
    INGRESS_RECEIPT_SCHEMA_V0,
    hash_v0,
    tx_hash_v0,
    validate_body_v0,
)
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.state.pools import compute_pool_id

REPORT_SCHEMA = "zenodex.zeno_ledger.make_testnet_bundle_report.v0"

DEFAULT_CHAIN_ID = "zeno-ledger-testnet-0"
DEFAULT_SEQUENCER_ID = "sequencer-testnet-0"
DEFAULT_TIME_MS = 1_778_730_000_000
DEFAULT_BOOTSTRAP_SENDER = "0x" + "aa" * 48
DEFAULT_TAGRS_ASSET_ID = "0x" + "11" * 32
DEFAULT_TZDEX_ASSET_ID = "0x" + "22" * 32
DEFAULT_ASSET0 = DEFAULT_TAGRS_ASSET_ID
DEFAULT_ASSET1 = DEFAULT_TZDEX_ASSET_ID
DEFAULT_RELEASE_TESTNET_TOKEN_SYMBOL = "tZDEX"


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _rel(root: Path, path: Path) -> str:
    return path.resolve().relative_to(root.resolve()).as_posix()


def _root(label: str, payload: object) -> str:
    return hash_v0(f"testnet_bundle_{label}", payload)


def _ingress_receipt_v0(
    *,
    chain_id: str,
    tx_hash: str,
    height: int,
    index: int,
    time_ms: int,
    sequencer_id: str,
) -> dict[str, Any]:
    body = {
        "schema": INGRESS_RECEIPT_SCHEMA_V0,
        "chain_id": chain_id,
        "tx_hash": tx_hash,
        "received_time_ms": time_ms,
        "received_sequence": height * 1_000 + index,
        "sequencer_id": sequencer_id,
        "status": "included",
        "height": height,
        "index": index,
        "reject_code": None,
    }
    return {**body, "receipt_hash": hash_v0("testnet_ingress_receipt_v0", body)}


def _empty_evidence_v0() -> dict[str, list[object]]:
    return {
        "upba_certificates": [],
        "price_grid_tables": [],
        "uniform_batch_hypergraph_roots": [],
        "oracle_packets": [],
        "proof_receipts": [],
        "rejection_receipts": [],
    }


def _body_with_transaction_v0(
    *,
    chain_id: str,
    height: int,
    time_ms: int,
    sequencer_id: str,
    tx: dict[str, Any],
    policy_id: str = "sovereign_public_cutoff_v0",
) -> dict[str, Any]:
    body = {
        "schema": BODY_SCHEMA_V0,
        "chain_id": chain_id,
        "height": height,
        "ingress": {
            "batch_cutoff": {
                "schema": BATCH_CUTOFF_SCHEMA_V0,
                "chain_id": chain_id,
                "height": height,
                "cutoff_time_ms": time_ms,
                "cutoff_sequence": height * 1_000,
                "sequencer_id": sequencer_id,
                "policy_id": policy_id,
                "policy_digest": _root("ingress_policy", {"chain_id": chain_id, "policy_id": policy_id}),
            },
            "ingress_receipts": [
                _ingress_receipt_v0(
                    chain_id=chain_id,
                    tx_hash=tx_hash_v0(tx),
                    height=height,
                    index=0,
                    time_ms=time_ms,
                    sequencer_id=sequencer_id,
                )
            ],
            "forced_inclusion_requests": [],
            "forced_inclusion_decisions": [],
        },
        "transactions": [tx],
        "settlement_envelopes": [],
        "evidence": _empty_evidence_v0(),
    }
    validate_body_v0(body)
    return body


def build_create_pool_body_v0(
    *,
    chain_id: str,
    height: int,
    time_ms: int,
    sequencer_id: str,
    sender_pubkey: str,
    asset0: str,
    asset1: str,
) -> dict[str, Any]:
    asset_a = min(asset0, asset1)
    asset_b = max(asset0, asset1)
    tx = {
        "tx_id": "bootstrap-create-pool-v0",
        "block_timestamp": max(0, int(time_ms) // 1000),
        "tx_sender_pubkey": sender_pubkey,
        "operations": {
            "2": [
                {
                    "module": "TauSwap",
                    "version": "0.1",
                    "kind": "CREATE_POOL",
                    "intent_id": _root("bootstrap_create_pool_intent", {"chain_id": chain_id}),
                    "sender_pubkey": sender_pubkey,
                    "deadline": 9_999_999_999,
                    "nonce": 1,
                    "asset0": asset_a,
                    "asset1": asset_b,
                    "fee_bps": 30,
                    "amount0": 100_000,
                    "amount1": 200_000,
                    "created_at": 1,
                }
            ]
        },
    }
    return _body_with_transaction_v0(
        chain_id=chain_id,
        height=height,
        time_ms=time_ms,
        sequencer_id=sequencer_id,
        tx=tx,
    )


def build_swap_body_v0(
    *,
    chain_id: str,
    height: int,
    time_ms: int,
    sequencer_id: str,
    sender_pubkey: str,
    asset0: str,
    asset1: str,
) -> dict[str, Any]:
    asset_a = min(asset0, asset1)
    asset_b = max(asset0, asset1)
    tx = {
        "tx_id": "bootstrap-swap-v0",
        "block_timestamp": max(0, int(time_ms) // 1000),
        "tx_sender_pubkey": sender_pubkey,
        "operations": {
            "2": [
                {
                    "module": "TauSwap",
                    "version": "0.1",
                    "kind": "SWAP_EXACT_IN",
                    "intent_id": _root("bootstrap_swap_intent", {"chain_id": chain_id}),
                    "sender_pubkey": sender_pubkey,
                    "deadline": 9_999_999_999,
                    "nonce": 2,
                    "pool_id": compute_pool_id(asset_a, asset_b, 30),
                    "asset_in": asset_a,
                    "asset_out": asset_b,
                    "amount_in": 1_000,
                    "min_amount_out": 1,
                    "recipient": sender_pubkey,
                }
            ]
        },
    }
    return _body_with_transaction_v0(
        chain_id=chain_id,
        height=height,
        time_ms=time_ms,
        sequencer_id=sequencer_id,
        tx=tx,
    )


def build_add_liquidity_body_v0(
    *,
    chain_id: str,
    height: int,
    time_ms: int,
    sequencer_id: str,
    sender_pubkey: str,
    asset0: str,
    asset1: str,
) -> dict[str, Any]:
    asset_a = min(asset0, asset1)
    asset_b = max(asset0, asset1)
    tx = {
        "tx_id": "bootstrap-add-liquidity-v0",
        "block_timestamp": max(0, int(time_ms) // 1000),
        "tx_sender_pubkey": sender_pubkey,
        "operations": {
            "2": [
                {
                    "module": "TauSwap",
                    "version": "0.1",
                    "kind": "ADD_LIQUIDITY",
                    "intent_id": _root("bootstrap_add_liquidity_intent", {"chain_id": chain_id}),
                    "sender_pubkey": sender_pubkey,
                    "deadline": 9_999_999_999,
                    "nonce": 3,
                    "pool_id": compute_pool_id(asset_a, asset_b, 30),
                    "amount0_desired": 1_000,
                    "amount1_desired": 2_000,
                    "amount0_min": 1,
                    "amount1_min": 1,
                    "recipient": sender_pubkey,
                }
            ]
        },
    }
    return _body_with_transaction_v0(
        chain_id=chain_id,
        height=height,
        time_ms=time_ms,
        sequencer_id=sequencer_id,
        tx=tx,
    )


def build_remove_liquidity_body_v0(
    *,
    chain_id: str,
    height: int,
    time_ms: int,
    sequencer_id: str,
    sender_pubkey: str,
    asset0: str,
    asset1: str,
) -> dict[str, Any]:
    asset_a = min(asset0, asset1)
    asset_b = max(asset0, asset1)
    tx = {
        "tx_id": "bootstrap-remove-liquidity-v0",
        "block_timestamp": max(0, int(time_ms) // 1000),
        "tx_sender_pubkey": sender_pubkey,
        "operations": {
            "2": [
                {
                    "module": "TauSwap",
                    "version": "0.1",
                    "kind": "REMOVE_LIQUIDITY",
                    "intent_id": _root("bootstrap_remove_liquidity_intent", {"chain_id": chain_id}),
                    "sender_pubkey": sender_pubkey,
                    "deadline": 9_999_999_999,
                    "nonce": 4,
                    "pool_id": compute_pool_id(asset_a, asset_b, 30),
                    "lp_amount": 100,
                    "amount0_min": 1,
                    "amount1_min": 1,
                    "recipient": sender_pubkey,
                }
            ]
        },
    }
    return _body_with_transaction_v0(
        chain_id=chain_id,
        height=height,
        time_ms=time_ms,
        sequencer_id=sequencer_id,
        tx=tx,
    )


def build_rejected_body_v0(
    *,
    chain_id: str,
    height: int,
    time_ms: int,
    sequencer_id: str,
) -> dict[str, Any]:
    tx = {
        "tx_id": "bootstrap-rejected-missing-operations-v0",
        "block_timestamp": max(0, int(time_ms) // 1000),
    }
    return _body_with_transaction_v0(
        chain_id=chain_id,
        height=height,
        time_ms=time_ms,
        sequencer_id=sequencer_id,
        tx=tx,
    )


def build_genesis_snapshot_v0(
    *,
    sender_pubkey: str,
    asset0: str,
    asset1: str,
    token_distribution: dict[str, Any] | None = None,
) -> dict[str, Any]:
    balances = BalanceTable()
    balances.set(sender_pubkey, min(asset0, asset1), 1_000_000_000)
    balances.set(sender_pubkey, max(asset0, asset1), 2_000_000_000)
    if token_distribution is not None:
        validate_protocol_token_distribution_v0(token_distribution)
        token_asset_id = str(token_distribution["token_asset_id"])
        for allocation in token_distribution["allocations"]:
            balances.add(
                str(allocation["recipient_pubkey"]),
                token_asset_id,
                int(allocation["amount"]),
            )
    state = DexState(balances=balances, pools={}, lp_balances=LPTable())
    return snapshot_from_state(state).data


def build_testnet_bundle_v0(
    *,
    out_dir: Path,
    chain_id: str,
    sequencer_id: str,
    time_ms: int,
    token_symbol: str,
    proof_required: bool,
    token_distribution_role_pubkeys: dict[str, str] | None = None,
) -> dict[str, Any]:
    engine_config_document = replay_engine_config_document_v0(
        DexEngineConfig(
            allow_missing_settlement=True,
            require_intent_signatures=False,
            allow_unsigned_intents_if_tx_sender_matches=True,
            chain_id=chain_id,
        )
    )
    config_digest = replay_engine_config_digest_v0(engine_config_document)
    sequencer_set_hash = _root("sequencer_set", {"sequencer_id": sequencer_id})
    module_versions_digest = _root("module_versions", {"schema": "zeno_ledger_v0"})
    token_asset_id = _root("token_asset", {"chain_id": chain_id, "symbol": token_symbol})
    token_distribution = build_protocol_token_distribution_v0(
        chain_id=chain_id,
        token_symbol=token_symbol,
        token_asset_id=token_asset_id,
        role_pubkeys=token_distribution_role_pubkeys,
        fallback_pubkey=DEFAULT_BOOTSTRAP_SENDER,
    )

    profile = sample_zeno_sovereign_testnet_profile_v0(
        chain_id=chain_id,
        config_digest=config_digest,
        sequencer_set_hash=sequencer_set_hash,
        token_symbol=token_symbol,
        token_asset_id=token_asset_id,
        proof_required=proof_required,
    )
    genesis = build_genesis_snapshot_v0(
        sender_pubkey=DEFAULT_BOOTSTRAP_SENDER,
        asset0=DEFAULT_ASSET0,
        asset1=DEFAULT_ASSET1,
        token_distribution=token_distribution,
    )
    body1 = build_create_pool_body_v0(
        chain_id=chain_id,
        height=1,
        time_ms=time_ms,
        sequencer_id=sequencer_id,
        sender_pubkey=DEFAULT_BOOTSTRAP_SENDER,
        asset0=DEFAULT_ASSET0,
        asset1=DEFAULT_ASSET1,
    )
    body2 = build_swap_body_v0(
        chain_id=chain_id,
        height=2,
        time_ms=time_ms + 1_000,
        sequencer_id=sequencer_id,
        sender_pubkey=DEFAULT_BOOTSTRAP_SENDER,
        asset0=DEFAULT_ASSET0,
        asset1=DEFAULT_ASSET1,
    )
    body3 = build_add_liquidity_body_v0(
        chain_id=chain_id,
        height=3,
        time_ms=time_ms + 2_000,
        sequencer_id=sequencer_id,
        sender_pubkey=DEFAULT_BOOTSTRAP_SENDER,
        asset0=DEFAULT_ASSET0,
        asset1=DEFAULT_ASSET1,
    )
    body4 = build_remove_liquidity_body_v0(
        chain_id=chain_id,
        height=4,
        time_ms=time_ms + 3_000,
        sequencer_id=sequencer_id,
        sender_pubkey=DEFAULT_BOOTSTRAP_SENDER,
        asset0=DEFAULT_ASSET0,
        asset1=DEFAULT_ASSET1,
    )
    body5 = build_rejected_body_v0(
        chain_id=chain_id,
        height=5,
        time_ms=time_ms + 4_000,
        sequencer_id=sequencer_id,
    )

    profile_path = out_dir / "profile.json"
    engine_config_path = out_dir / "engine_config.json"
    genesis_path = out_dir / "genesis_snapshot.json"
    token_distribution_path = out_dir / "token_distribution.json"
    body1_path = out_dir / "bodies" / "1_create_pool.json"
    body2_path = out_dir / "bodies" / "2_swap.json"
    body3_path = out_dir / "bodies" / "3_add_liquidity.json"
    body4_path = out_dir / "bodies" / "4_remove_liquidity.json"
    body5_path = out_dir / "bodies" / "5_rejected.json"
    ledger_out_dir = out_dir / "ledger"
    attestation_path = out_dir / "watcher_attestations" / "bootstrap_range_1_5.json"
    mirror_index_path = out_dir / "mirror_index.json"
    manifest_path = out_dir / "manifest.json"

    _write_json(engine_config_path, engine_config_document)

    def run_local_command(
        *,
        body_path: Path,
        command_time_ms: int,
        prev_height: int | None = None,
    ) -> list[str]:
        command = [
            "python3",
            "tools/zeno_ledger_run_local.py",
            "--body",
            _rel(out_dir, body_path),
            "--out-dir",
            _rel(out_dir, ledger_out_dir),
            "--time-ms",
            str(command_time_ms),
        ]
        if prev_height is None:
            command.extend(["--pre-snapshot", _rel(out_dir, genesis_path)])
        else:
            command.extend(
                [
                    "--prev-header",
                    _rel(out_dir, ledger_out_dir / "headers" / f"{prev_height}.json"),
                    "--pre-snapshot",
                    _rel(out_dir, ledger_out_dir / "snapshots" / f"{prev_height}.json"),
                    "--omit-pre-snapshot-output",
                ]
            )
        command.extend(
            [
                "--allow-missing-settlement",
                "--disable-intent-signatures",
                "--allow-unsigned-intents-if-tx-sender-matches",
                "--sequencer-set-hash",
                sequencer_set_hash,
                "--config-digest",
                config_digest,
                "--module-versions-digest",
                module_versions_digest,
            ]
        )
        return command

    run_commands = [
        run_local_command(body_path=body1_path, command_time_ms=time_ms),
        run_local_command(body_path=body2_path, command_time_ms=time_ms + 1_000, prev_height=1),
        run_local_command(body_path=body3_path, command_time_ms=time_ms + 2_000, prev_height=2),
        run_local_command(body_path=body4_path, command_time_ms=time_ms + 3_000, prev_height=3),
        run_local_command(body_path=body5_path, command_time_ms=time_ms + 4_000, prev_height=4),
    ]
    run_command = run_commands[0]
    verify_command = [
        "python3",
        "tools/zeno_ledger_verify.py",
        "--headers-dir",
        _rel(out_dir, ledger_out_dir / "headers"),
        "--bodies-dir",
        _rel(out_dir, ledger_out_dir / "bodies"),
        "--checkpoints-dir",
        _rel(out_dir, ledger_out_dir / "checkpoints"),
        "--profile",
        _rel(out_dir, profile_path),
        "--from-height",
        "1",
        "--to-height",
        "5",
        "--require-state-replay",
        "--require-rejection-receipt-replay",
        "--pre-snapshots-dir",
        _rel(out_dir, ledger_out_dir / "pre_snapshots"),
        "--engine-config",
        _rel(out_dir, engine_config_path),
    ]
    attest_command = [
        "python3",
        "tools/zeno_ledger_attest.py",
        "--headers-dir",
        _rel(out_dir, ledger_out_dir / "headers"),
        "--bodies-dir",
        _rel(out_dir, ledger_out_dir / "bodies"),
        "--checkpoints-dir",
        _rel(out_dir, ledger_out_dir / "checkpoints"),
        "--profile",
        _rel(out_dir, profile_path),
        "--from-height",
        "1",
        "--to-height",
        "5",
        "--require-state-replay",
        "--require-rejection-receipt-replay",
        "--pre-snapshots-dir",
        _rel(out_dir, ledger_out_dir / "pre_snapshots"),
        "--engine-config",
        _rel(out_dir, engine_config_path),
        "--watcher-id",
        "bootstrap-watcher-0",
        "--observed-time-ms",
        str(time_ms + 5_000),
        "--out",
        _rel(out_dir, attestation_path),
    ]
    mirror_index_command = [
        "python3",
        "tools/zeno_ledger_make_mirror_index.py",
        "--manifest",
        _rel(out_dir, manifest_path),
        "--mirror-root",
        ".",
        "--out",
        _rel(out_dir, mirror_index_path),
    ]
    manifest = {
        "schema": "zenodex.zeno_ledger.testnet_bundle.v0",
        "chain_id": chain_id,
        "sequencer_id": sequencer_id,
        "time_ms": time_ms,
        "config_digest": config_digest,
        "module_versions_digest": module_versions_digest,
        "sequencer_set_hash": sequencer_set_hash,
        "token_asset_id": token_asset_id,
        "token_symbol": token_symbol,
        "token_distribution_path": _rel(out_dir, token_distribution_path),
        "token_distribution_hash": token_distribution["distribution_hash"],
        "profile_path": _rel(out_dir, profile_path),
        "engine_config_path": _rel(out_dir, engine_config_path),
        "genesis_snapshot_path": _rel(out_dir, genesis_path),
        "body_paths": [
            _rel(out_dir, body1_path),
            _rel(out_dir, body2_path),
            _rel(out_dir, body3_path),
            _rel(out_dir, body4_path),
            _rel(out_dir, body5_path),
        ],
        "first_body_path": _rel(out_dir, body1_path),
        "ledger_out_dir": _rel(out_dir, ledger_out_dir),
        "run_commands": run_commands,
        "run_command": run_command,
        "verify_command": verify_command,
        "attest_command": attest_command,
        "attestation_path": _rel(out_dir, attestation_path),
        "mirror_index_command": mirror_index_command,
        "mirror_index_path": _rel(out_dir, mirror_index_path),
    }

    _write_json(profile_path, profile)
    _write_json(genesis_path, genesis)
    _write_json(token_distribution_path, token_distribution)
    _write_json(body1_path, body1)
    _write_json(body2_path, body2)
    _write_json(body3_path, body3)
    _write_json(body4_path, body4)
    _write_json(body5_path, body5)
    _write_json(manifest_path, manifest)
    return {
        "schema": REPORT_SCHEMA,
        "ok": True,
        "status": "accepted",
        "manifest_path": str(manifest_path),
        "manifest": manifest,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build a deterministic sovereign ZenoLedger testnet bundle")
    parser.add_argument("--out-dir", required=True, type=Path)
    parser.add_argument("--chain-id", default=DEFAULT_CHAIN_ID)
    parser.add_argument("--sequencer-id", default=DEFAULT_SEQUENCER_ID)
    parser.add_argument("--time-ms", type=int, default=DEFAULT_TIME_MS)
    parser.add_argument("--token-symbol", default=DEFAULT_PROTOCOL_TOKEN_SYMBOL)
    parser.add_argument("--proof-required", action="store_true")
    parser.add_argument("--fixture-key-bundle", type=Path)
    args = parser.parse_args(argv)

    try:
        report = build_testnet_bundle_v0(
            out_dir=args.out_dir,
            chain_id=args.chain_id,
            sequencer_id=args.sequencer_id,
            time_ms=args.time_ms,
            token_symbol=args.token_symbol,
            proof_required=bool(args.proof_required),
            token_distribution_role_pubkeys=load_role_pubkeys_from_key_bundle_v0(args.fixture_key_bundle),
        )
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
