#!/usr/bin/env python3
"""Run a minimal real Risc0 ZenoDEX spot proof generate/verify smoke.

This is intentionally opt-in and heavier than normal unit tests. It builds the
Risc0 guest method with `RISC0_FORCE_BUILD=1`, proves the empty v1 spot state
transition plus the current supported spot v1 operation families, verifies
the returned receipts with block/context checks, and prints a compact JSON
report. The full receipts are written only to the selected output directory.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any


EMPTY_SNAPSHOT_V1: dict[str, Any] = {
    "version": 1,
    "balances": [],
    "pools": [],
    "lp_balances": [],
    "fee_accumulator": {"dust": 0},
    "vault": None,
    "oracle": None,
}

ASSET0 = "0x" + "11" * 32
ASSET1 = "0x" + "22" * 32
SENDER = "0x" + "aa" * 48
RECIPIENT = "0x" + "bb" * 48
POOL_ID = "0xcc9c112f06b5ba4cd276419759e7b3e203ede2c64aa45ba75e24fa4609d9c686"


def _canonical_json_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def _snapshot_hash(snapshot: dict[str, Any]) -> str:
    return hashlib.sha256(_canonical_json_bytes(snapshot)).hexdigest()


def _pool_entry(*, reserve0: int, reserve1: int) -> dict[str, Any]:
    return {
        "pool_id": POOL_ID,
        "asset0": ASSET0,
        "asset1": ASSET1,
        "reserve0": reserve0,
        "reserve1": reserve1,
        "fee_bps": 30,
        "lp_supply": 10_000,
        "status": "ACTIVE",
        "created_at": 0,
    }


def _empty_snapshot_copy() -> dict[str, Any]:
    return json.loads(json.dumps(EMPTY_SNAPSHOT_V1))


def _smoke_cases() -> dict[str, dict[str, Any]]:
    empty_hash = _snapshot_hash(EMPTY_SNAPSHOT_V1)

    faucet_pre = _empty_snapshot_copy()
    faucet_post = _empty_snapshot_copy()
    faucet_post["balances"] = [
        {"pubkey": SENDER, "asset": ASSET0, "amount": 1_000},
    ]
    faucet_tx = {
        "sender_pubkey": SENDER,
        "operations": {
            "4": {
                "mint": [
                    [SENDER, ASSET0, 1_000],
                ]
            }
        },
    }

    create_pre = _empty_snapshot_copy()
    create_pre["balances"] = [
        {"pubkey": SENDER, "asset": ASSET0, "amount": 10_000},
        {"pubkey": SENDER, "asset": ASSET1, "amount": 20_000},
    ]
    create_post = _empty_snapshot_copy()
    create_post["balances"] = [
        {"pubkey": SENDER, "asset": ASSET1, "amount": 10_000},
    ]
    create_post["pools"] = [_pool_entry(reserve0=10_000, reserve1=10_000)]
    create_post["lp_balances"] = [
        {"pubkey": "0x" + "00" * 48, "pool_id": POOL_ID, "amount": 1_000},
        {"pubkey": SENDER, "pool_id": POOL_ID, "amount": 9_000},
    ]
    create_tx = {
        "sender_pubkey": SENDER,
        "operations": {
            "2": [
                {
                    "module": "TauSwap",
                    "version": "v1",
                    "kind": "CREATE_POOL",
                    "intent_id": "create-1",
                    "sender_pubkey": SENDER,
                    "deadline": 100,
                    "asset0": ASSET0,
                    "asset1": ASSET1,
                    "fee_bps": 30,
                    "amount0": 10_000,
                    "amount1": 10_000,
                }
            ]
        },
    }

    swap_pre = _empty_snapshot_copy()
    swap_pre["balances"] = [
        {"pubkey": SENDER, "asset": ASSET0, "amount": 1_000},
    ]
    swap_pre["pools"] = [_pool_entry(reserve0=10_000, reserve1=10_000)]
    swap_post = _empty_snapshot_copy()
    swap_post["balances"] = [
        {"pubkey": RECIPIENT, "asset": ASSET1, "amount": 906},
    ]
    swap_post["pools"] = [_pool_entry(reserve0=11_000, reserve1=9_094)]
    swap_tx = {
        "sender_pubkey": SENDER,
        "operations": {
            "2": [
                {
                    "module": "TauSwap",
                    "version": "v1",
                    "kind": "SWAP_EXACT_IN",
                    "intent_id": "swap-1",
                    "sender_pubkey": SENDER,
                    "deadline": 100,
                    "pool_id": POOL_ID,
                    "asset_in": ASSET0,
                    "asset_out": ASSET1,
                    "amount_in": 1_000,
                    "min_amount_out": 900,
                    "recipient": RECIPIENT,
                }
            ]
        },
    }

    return {
        "empty": {
            "pre_snapshot": None,
            "pre_hash": "",
            "transactions": [],
            "post_hash": empty_hash,
        },
        "faucet_mint": {
            "pre_snapshot": faucet_pre,
            "pre_hash": _snapshot_hash(faucet_pre),
            "transactions": [faucet_tx],
            "post_hash": _snapshot_hash(faucet_post),
        },
        "create_pool": {
            "pre_snapshot": create_pre,
            "pre_hash": _snapshot_hash(create_pre),
            "transactions": [create_tx],
            "post_hash": _snapshot_hash(create_post),
        },
        "swap_exact_in": {
            "pre_snapshot": swap_pre,
            "pre_hash": _snapshot_hash(swap_pre),
            "transactions": [swap_tx],
            "post_hash": _snapshot_hash(swap_post),
        },
    }


def _run_cli(*, repo: Path, request: dict[str, Any], target_dir: Path, timeout: int) -> dict[str, Any]:
    env = os.environ.copy()
    env["RISC0_FORCE_BUILD"] = "1"
    env["CARGO_TARGET_DIR"] = str(target_dir)
    proc = subprocess.run(
        [
            "cargo",
            "run",
            "--manifest-path",
            str(repo / "zk/state_proof_risc0/Cargo.toml"),
            "-q",
            "-p",
            "tau-state-proof-risc0-cli",
        ],
        input=json.dumps(request, separators=(",", ":")),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        cwd=repo,
        env=env,
        timeout=timeout,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            "tau-state-proof-risc0-cli failed\n"
            f"exit={proc.returncode}\n"
            f"stdout={proc.stdout[-4000:]}\n"
            f"stderr={proc.stderr[-4000:]}"
        )
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"CLI returned invalid JSON: {exc}\nstdout={proc.stdout[-4000:]}") from exc


def _run_case(
    *,
    name: str,
    case: dict[str, Any],
    repo: Path,
    out_dir: Path,
    target_dir: Path,
    timeout: int,
) -> dict[str, Any]:
    state_hash = "11" * 32
    app_state_pre = ""
    if case["pre_snapshot"] is not None:
        app_state_pre = _canonical_json_bytes(case["pre_snapshot"]).decode("utf-8")

    generate_request = {
        "schema": "tau_state_proof_request",
        "schema_version": 1,
        "state_hash": state_hash,
        "block": {"header": {"timestamp": 1}, "transactions": case["transactions"]},
        "tau_state": {"app_hash": case["post_hash"]},
        "context": {
            "app_state_pre": app_state_pre,
            "app_hash_pre": case["pre_hash"],
            "chain_balances_post": {},
        },
    }
    proof = _run_cli(repo=repo, request=generate_request, target_dir=target_dir, timeout=timeout)
    proof_path = out_dir / f"{name}_tau_state_proof.json"
    proof_path.write_text(json.dumps(proof, sort_keys=True, indent=2) + "\n", encoding="utf-8")

    verify_request = {
        "schema": "tau_state_proof_verify",
        "schema_version": 1,
        "state_hash": state_hash,
        "proof": proof,
        "block": {"header": {"timestamp": 1}, "transactions": case["transactions"]},
        "tau_state": {"app_hash": case["post_hash"]},
        "context": {
            "app_hash_pre": case["pre_hash"],
            "block_timestamp": 1,
        },
    }
    verify = _run_cli(repo=repo, request=verify_request, target_dir=target_dir, timeout=timeout)
    if verify.get("ok") is not True:
        raise RuntimeError(f"receipt verification rejected: {verify}")

    meta = proof.get("meta") if isinstance(proof.get("meta"), dict) else {}
    return {
        "case": name,
        "ok": True,
        "proof_type": proof.get("proof_type"),
        "state_hash": proof.get("state_hash"),
        "post_app_hash": meta.get("post_app_hash"),
        "pre_app_hash": meta.get("pre_app_hash"),
        "txs_commitment": meta.get("txs_commitment"),
        "risc0_image_id": meta.get("risc0_image_id"),
        "proof_base64_len": len(proof.get("proof", "")) if isinstance(proof.get("proof"), str) else 0,
        "proof_path": str(proof_path),
    }


def run_smoke(*, repo: Path, out_dir: Path, target_dir: Path, timeout: int, case_name: str) -> dict[str, Any]:
    out_dir.mkdir(parents=True, exist_ok=True)
    cases = _smoke_cases()
    selected = list(cases) if case_name == "all" else [case_name]
    unknown = [c for c in selected if c not in cases]
    if unknown:
        raise ValueError(f"unknown smoke case(s): {', '.join(unknown)}")

    case_reports = [
        _run_case(
            name=name,
            case=cases[name],
            repo=repo,
            out_dir=out_dir,
            target_dir=target_dir,
            timeout=timeout,
        )
        for name in selected
    ]

    report = {
        "schema": "zenodex.risc0_real_proof_smoke.v0",
        "ok": True,
        "case_count": len(case_reports),
        "cases": case_reports,
    }
    report_path = out_dir / "real_proof_smoke_report.json"
    report_path.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--out-dir", type=Path, default=Path("/tmp/zenodex_risc0_real_proof_smoke"))
    parser.add_argument("--target-dir", type=Path, default=Path("/tmp/zenodex_risc0_force_target"))
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument(
        "--case",
        choices=("empty", "faucet_mint", "create_pool", "swap_exact_in", "all"),
        default="empty",
    )
    args = parser.parse_args(argv)

    report = run_smoke(
        repo=args.repo.resolve(),
        out_dir=args.out_dir.resolve(),
        target_dir=args.target_dir.resolve(),
        timeout=int(args.timeout),
        case_name=args.case,
    )
    print(json.dumps(report, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
