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

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.proof_toolchain_lock import proof_toolchain_lock_hash_v0  # noqa: E402
from src.integration.zeno_ledger_v0 import (  # noqa: E402
    BATCH_CUTOFF_SCHEMA_V0,
    BODY_SCHEMA_V0,
    EVIDENCE_KEYS_V0,
    INGRESS_RECEIPT_SCHEMA_V0,
    ZERO_ROOT_V0,
    build_header_v0,
    canonical_body_root_v0,
    compute_app_hash_v0,
    compute_evidence_root_v0,
    compute_ingress_root_v0,
    compute_tx_root_v0,
    hash_v0,
    proof_metadata_hash_v0,
    tx_hash_v0,
    validate_header_body_roots_v0,
    validate_proof_metadata_header_binding_v0,
)
from tools.zeno_ledger_risc0_proof_metadata import (  # noqa: E402
    HEADER_DERIVED_FIELDS,
    build_header_derived_risc0_proof_metadata_diagnostic_v0,
)

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


def _json_clone(value: Any) -> Any:
    return json.loads(json.dumps(value, sort_keys=True, separators=(",", ":")))


def _root(label: str, value: Any) -> str:
    return hash_v0("risc0_real_proof_smoke_binding_v0", {"label": label, "value": value})


def _with_0x(hex_value: str) -> str:
    return hex_value if hex_value.startswith("0x") else f"0x{hex_value}"


def _strip_0x(hex_value: str) -> str:
    return hex_value[2:] if hex_value.startswith("0x") else hex_value


def _pool_entry(*, reserve0: int, reserve1: int, lp_supply: int = 10_000) -> dict[str, Any]:
    return {
        "pool_id": POOL_ID,
        "asset0": ASSET0,
        "asset1": ASSET1,
        "reserve0": reserve0,
        "reserve1": reserve1,
        "fee_bps": 30,
        "lp_supply": lp_supply,
        "status": "ACTIVE",
        "created_at": 0,
    }


def _empty_snapshot_copy() -> dict[str, Any]:
    return _json_clone(EMPTY_SNAPSHOT_V1)


def _ledger_evidence() -> dict[str, list[Any]]:
    return {key: [] for key in EVIDENCE_KEYS_V0}


def _ingress_receipt(*, chain_id: str, height: int, index: int, tx_hash: str) -> dict[str, Any]:
    body = {
        "schema": INGRESS_RECEIPT_SCHEMA_V0,
        "chain_id": chain_id,
        "tx_hash": tx_hash,
        "received_time_ms": 1_778_730_000_000 + height * 100 + index,
        "received_sequence": height * 10_000 + index,
        "sequencer_id": "risc0-smoke-sequencer-0",
        "status": "included",
        "height": height,
        "index": index,
        "reject_code": None,
    }
    return {
        **body,
        "receipt_hash": hash_v0("risc0_real_proof_smoke_ingress_receipt_v0", body),
    }


def _ledger_body_for_case(*, name: str, case: dict[str, Any], height: int) -> dict[str, Any]:
    chain_id = "zenodex-risc0-spot-smoke-v0"
    transactions = _json_clone(case["transactions"])
    body = {
        "schema": BODY_SCHEMA_V0,
        "chain_id": chain_id,
        "height": height,
        "ingress": {
            "batch_cutoff": {
                "schema": BATCH_CUTOFF_SCHEMA_V0,
                "chain_id": chain_id,
                "height": height,
                "cutoff_time_ms": 1_778_730_000_000 + height * 100,
                "cutoff_sequence": height * 10_000 + len(transactions),
                "sequencer_id": "risc0-smoke-sequencer-0",
                "policy_id": "risc0_spot_smoke_v0",
                "policy_digest": _root("ingress-policy", name),
            },
            "ingress_receipts": [
                _ingress_receipt(
                    chain_id=chain_id,
                    height=height,
                    index=index,
                    tx_hash=tx_hash_v0(tx),
                )
                for index, tx in enumerate(transactions)
            ],
            "forced_inclusion_requests": [],
            "forced_inclusion_decisions": [],
        },
        "transactions": transactions,
        "settlement_envelopes": [],
        "evidence": _ledger_evidence(),
    }
    return body


def _ledger_header_for_case(
    *,
    name: str,
    body: dict[str, Any],
    proof: dict[str, Any],
    proof_journal_hash: str,
) -> dict[str, Any]:
    meta = proof.get("meta")
    if not isinstance(meta, dict):
        raise ValueError("proof meta must be an object")
    pre_hash = meta.get("pre_app_hash")
    post_hash = meta.get("post_app_hash")
    if not isinstance(pre_hash, str) or not isinstance(post_hash, str):
        raise ValueError("proof app hashes must be strings")

    pre_state_root = _root("pre-state-absent", name) if pre_hash == "" else _with_0x(pre_hash)
    post_state_root = _with_0x(post_hash)
    evidence_root = compute_evidence_root_v0(body["evidence"])
    config_digest = _root("config", name)
    module_versions_digest = _root("modules", name)
    app_hash = compute_app_hash_v0(
        {
            "chain_id": body["chain_id"],
            "height": body["height"],
            "post_state_root": post_state_root,
            "evidence_root": evidence_root,
            "config_digest": config_digest,
            "module_versions_digest": module_versions_digest,
        }
    )
    return build_header_v0(
        chain_id=str(body["chain_id"]),
        height=int(body["height"]),
        time_ms=1_778_730_000_000 + int(body["height"]) * 100,
        prev_header_hash=ZERO_ROOT_V0,
        sequencer_set_hash=_root("sequencer-set", name),
        ingress_root=compute_ingress_root_v0(body["ingress"]),
        tx_root=compute_tx_root_v0(body["transactions"]),
        pre_state_root=pre_state_root,
        post_state_root=post_state_root,
        app_hash=app_hash,
        evidence_root=evidence_root,
        body_root=canonical_body_root_v0(body),
        data_availability_root=_root("data-availability", name),
        proof_journal_hash=proof_journal_hash,
        config_digest=config_digest,
        module_versions_digest=module_versions_digest,
        signature_set_root=ZERO_ROOT_V0,
    )


def _ledger_binding_for_case(
    *,
    name: str,
    case: dict[str, Any],
    proof: dict[str, Any],
    repo: Path,
    out_dir: Path,
    height: int,
) -> dict[str, Any]:
    body = _ledger_body_for_case(name=name, case=case, height=height)
    header_unbound = _ledger_header_for_case(
        name=name,
        body=body,
        proof=proof,
        proof_journal_hash=ZERO_ROOT_V0,
    )
    metadata = build_header_derived_risc0_proof_metadata_diagnostic_v0(
        proof_envelope=proof,
        header=header_unbound,
        conflict_schedule_hash=_root("conflict-schedule", name),
        feature_suite_hash=_root("feature-suite", name),
        dependency_lock_hash=_root("dependency-lock", name),
        toolchain_lock_hash=proof_toolchain_lock_hash_v0(repo),
    )
    proof_journal_hash = proof_metadata_hash_v0(metadata)
    header = _ledger_header_for_case(
        name=name,
        body=body,
        proof=proof,
        proof_journal_hash=proof_journal_hash,
    )
    validate_header_body_roots_v0(header, body)
    validate_proof_metadata_header_binding_v0(metadata, header)

    meta = proof.get("meta")
    if not isinstance(meta, dict):
        raise TypeError(f"{name}: proof meta must be an object")
    post_state_root_checked = _strip_0x(str(header["post_state_root"])) == meta["post_app_hash"]
    pre_state_root_checked = (
        meta["pre_app_hash"] == ""
        or _strip_0x(str(header["pre_state_root"])) == meta["pre_app_hash"]
    )
    if not post_state_root_checked:
        raise ValueError(f"{name}: proof post_app_hash/header post_state_root mismatch")
    if not pre_state_root_checked:
        raise ValueError(f"{name}: proof pre_app_hash/header pre_state_root mismatch")

    body_path = out_dir / f"{name}_zeno_ledger_body.json"
    header_path = out_dir / f"{name}_zeno_ledger_header.json"
    metadata_path = out_dir / f"{name}_risc0_proof_metadata.json"
    body_path.write_text(json.dumps(body, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    header_path.write_text(json.dumps(header, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    metadata_path.write_text(json.dumps(metadata, sort_keys=True, indent=2) + "\n", encoding="utf-8")

    return {
        "schema": "zenodex.risc0_real_proof_smoke.ledger_binding.v0",
        "ok": True,
        "status": "non_authoritative_header_derived_metadata",
        "authority_scope": "none",
        "header_derived_fields": list(HEADER_DERIVED_FIELDS),
        "proof_authority_satisfied": False,
        "settlement_authority": False,
        "production_authority": False,
        "header_bound": True,
        "body_checked": True,
        "post_state_root_checked": post_state_root_checked,
        "pre_state_root_checked": pre_state_root_checked,
        "body_tx_count": len(body["transactions"]),
        "body_path": str(body_path),
        "header_path": str(header_path),
        "metadata_path": str(metadata_path),
        "proof_journal_hash": proof_journal_hash,
        "pre_state_root": str(header["pre_state_root"]),
        "post_state_root": str(header["post_state_root"]),
        "tx_root": str(header["tx_root"]),
        "body_root": str(header["body_root"]),
        "evidence_root": str(header["evidence_root"]),
        "ledger_app_hash": str(header["app_hash"]),
    }



def _smoke_cases() -> dict[str, dict[str, Any]]:
    empty_hash = _snapshot_hash(EMPTY_SNAPSHOT_V1)

    faucet_pre = _empty_snapshot_copy()
    faucet_post = _empty_snapshot_copy()
    faucet_post["balances"] = [
        {"pubkey": SENDER, "asset": ASSET0, "amount": 1_000},
    ]
    faucet_tx = {
        "sender_pubkey": SENDER,
        "nonce": 0,
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
        "nonce": 0,
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
        "nonce": 0,
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

    add_pre = _empty_snapshot_copy()
    add_pre["balances"] = [
        {"pubkey": SENDER, "asset": ASSET0, "amount": 1_000},
        {"pubkey": SENDER, "asset": ASSET1, "amount": 2_000},
    ]
    add_pre["pools"] = [_pool_entry(reserve0=10_000, reserve1=10_000)]
    add_post = _empty_snapshot_copy()
    add_post["balances"] = [
        {"pubkey": SENDER, "asset": ASSET1, "amount": 1_000},
    ]
    add_post["pools"] = [_pool_entry(reserve0=11_000, reserve1=11_000, lp_supply=11_000)]
    add_post["lp_balances"] = [
        {"pubkey": SENDER, "pool_id": POOL_ID, "amount": 1_000},
    ]
    add_tx = {
        "sender_pubkey": SENDER,
        "nonce": 0,
        "operations": {
            "2": [
                {
                    "module": "TauSwap",
                    "version": "v1",
                    "kind": "ADD_LIQUIDITY",
                    "intent_id": "add-1",
                    "sender_pubkey": SENDER,
                    "deadline": 100,
                    "pool_id": POOL_ID,
                    "amount0_desired": 1_000,
                    "amount1_desired": 2_000,
                    "amount0_min": 0,
                    "amount1_min": 0,
                    "recipient": SENDER,
                }
            ]
        },
    }

    remove_pre = _empty_snapshot_copy()
    remove_pre["pools"] = [_pool_entry(reserve0=10_000, reserve1=10_000)]
    remove_pre["lp_balances"] = [
        {"pubkey": SENDER, "pool_id": POOL_ID, "amount": 1_000},
    ]
    remove_post = _empty_snapshot_copy()
    remove_post["balances"] = [
        {"pubkey": SENDER, "asset": ASSET0, "amount": 1_000},
        {"pubkey": SENDER, "asset": ASSET1, "amount": 1_000},
    ]
    remove_post["pools"] = [_pool_entry(reserve0=9_000, reserve1=9_000, lp_supply=9_000)]
    remove_tx = {
        "sender_pubkey": SENDER,
        "nonce": 0,
        "operations": {
            "2": [
                {
                    "module": "TauSwap",
                    "version": "v1",
                    "kind": "REMOVE_LIQUIDITY",
                    "intent_id": "remove-1",
                    "sender_pubkey": SENDER,
                    "deadline": 100,
                    "pool_id": POOL_ID,
                    "lp_amount": 1_000,
                    "amount0_min": 0,
                    "amount1_min": 0,
                    "recipient": SENDER,
                }
            ]
        },
    }

    combo_pre = _empty_snapshot_copy()
    combo_pre["balances"] = [
        {"pubkey": SENDER, "asset": ASSET0, "amount": 20_000},
        {"pubkey": SENDER, "asset": ASSET1, "amount": 20_000},
    ]
    combo_create_tx = json.loads(json.dumps(create_tx))
    combo_add_tx = json.loads(json.dumps(add_tx))
    combo_add_tx["nonce"] = 1
    combo_add_tx["operations"]["2"][0]["intent_id"] = "combo-add-1"
    combo_swap_tx = json.loads(json.dumps(swap_tx))
    combo_swap_tx["nonce"] = 2
    combo_swap_tx["operations"]["2"][0]["intent_id"] = "combo-swap-1"
    combo_remove_tx = json.loads(json.dumps(remove_tx))
    combo_remove_tx["nonce"] = 3
    combo_remove_tx["operations"]["2"][0]["intent_id"] = "combo-remove-1"
    combo_remove_tx["operations"]["2"][0]["lp_amount"] = 500
    combo_post = _empty_snapshot_copy()
    combo_post["balances"] = [
        {"pubkey": SENDER, "asset": ASSET0, "amount": 8_545},
        {"pubkey": SENDER, "asset": ASSET1, "amount": 9_458},
        {"pubkey": RECIPIENT, "asset": ASSET1, "amount": 914},
    ]
    combo_post["pools"] = [_pool_entry(reserve0=11_455, reserve1=9_628, lp_supply=10_500)]
    combo_post["lp_balances"] = [
        {"pubkey": "0x" + "00" * 48, "pool_id": POOL_ID, "amount": 1_000},
        {"pubkey": SENDER, "pool_id": POOL_ID, "amount": 9_500},
    ]

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
        "add_liquidity": {
            "pre_snapshot": add_pre,
            "pre_hash": _snapshot_hash(add_pre),
            "transactions": [add_tx],
            "post_hash": _snapshot_hash(add_post),
        },
        "remove_liquidity": {
            "pre_snapshot": remove_pre,
            "pre_hash": _snapshot_hash(remove_pre),
            "transactions": [remove_tx],
            "post_hash": _snapshot_hash(remove_post),
        },
        "spot_block_liquidity_cycle": {
            "pre_snapshot": combo_pre,
            "pre_hash": _snapshot_hash(combo_pre),
            "transactions": [combo_create_tx, combo_add_tx, combo_swap_tx, combo_remove_tx],
            "post_hash": _snapshot_hash(combo_post),
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
    height: int,
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
    ledger_binding = _ledger_binding_for_case(
        name=name,
        case=case,
        proof=proof,
        repo=repo,
        out_dir=out_dir,
        height=height,
    )
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
        "ledger_binding": ledger_binding,
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
            height=index,
        )
        for index, name in enumerate(selected, start=1)
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
        choices=(
            "empty",
            "faucet_mint",
            "create_pool",
            "swap_exact_in",
            "add_liquidity",
            "remove_liquidity",
            "spot_block_liquidity_cycle",
            "all",
        ),
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
