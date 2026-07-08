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
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.risc0_tx_execution_order import TxExecutionOrderInputV1  # noqa: E402
from src.integration.proof_toolchain_lock import proof_toolchain_lock_hash_v0  # noqa: E402
from src.integration.risc0_route_body_projection import (  # noqa: E402
    project_route_body_transactions_to_proof_v1,
    route_body_projection_contract_hash_v1,
    route_body_projection_contract_v1,
)
from src.integration.risc0_tx_order_body_summary import (  # noqa: E402
    apply_route_order_receipt_policy_to_body_v1,
    route_order_receipt_requirement_for_case_v1,
    tx_order_inputs_for_case_v1,
)
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
from tools.risc0_runtime_env import proof_runner_env  # noqa: E402
from tools.zeno_ledger_risc0_proof_metadata import build_risc0_proof_metadata_v0  # noqa: E402

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
OTHER_SENDER = "0x" + "dd" * 48
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


def _route_quote_receipt_hash_v1(
    *,
    kind: str,
    asset_in: str,
    asset_out: str,
    total_amount_in: int,
    total_min_amount_out: int,
    total_amount_out: int,
    total_max_amount_in: int,
    leg_indices: list[int],
    legs: list[dict[str, Any]],
    pools_by_id: dict[str, dict[str, Any]],
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: str | None = None,
) -> str:
    hasher = hashlib.sha256()
    hasher.update(b"zenodex.risc0.route_quote_receipt_binding.v1:")
    _hash_write_str(hasher, kind)
    _hash_write_str(hasher, asset_in)
    _hash_write_str(hasher, asset_out)
    _hash_write_u128(hasher, total_amount_in)
    _hash_write_u128(hasher, total_min_amount_out)
    _hash_write_u128(hasher, total_amount_out)
    _hash_write_u128(hasher, total_max_amount_in)
    _hash_write_u32(hasher, protocol_fee_share_bps)
    _hash_write_opt_str(hasher, protocol_fee_recipient_pubkey)
    _hash_write_u32(hasher, len(leg_indices))
    for index in leg_indices:
        _hash_write_u32(hasher, index)
    _hash_write_u32(hasher, len(legs))
    for leg in legs:
        hops = leg.get("hops")
        if not isinstance(hops, list) or len(hops) != 1:
            raise ValueError("route smoke supports one-hop route legs only")
        _hash_write_u32(hasher, 1)
        hop = hops[0]
        if not isinstance(hop, dict):
            raise TypeError("route hop must be an object")
        pool_id = hop.get("pool_id")
        if not isinstance(pool_id, str):
            raise TypeError("route hop pool_id must be a string")
        pool = pools_by_id[pool_id]
        _hash_write_str(hasher, str(pool["pool_id"]))
        _hash_write_str(hasher, str(pool["asset0"]))
        _hash_write_str(hasher, str(pool["asset1"]))
        _hash_write_u128(hasher, int(pool["reserve0"]))
        _hash_write_u128(hasher, int(pool["reserve1"]))
        _hash_write_u32(hasher, int(pool["fee_bps"]))
        _hash_write_u128(hasher, int(pool["lp_supply"]))
        _hash_write_str(hasher, str(pool["status"]))
        _hash_write_u64(hasher, int(pool["created_at"]))
    return "0x" + hasher.hexdigest()


def _hash_write_u32(hasher: "hashlib._Hash", value: int) -> None:
    hasher.update(int(value).to_bytes(4, byteorder="big", signed=False))


def _hash_write_u64(hasher: "hashlib._Hash", value: int) -> None:
    hasher.update(int(value).to_bytes(8, byteorder="big", signed=False))


def _hash_write_u128(hasher: "hashlib._Hash", value: int) -> None:
    hasher.update(int(value).to_bytes(16, byteorder="big", signed=False))


def _hash_write_str(hasher: "hashlib._Hash", value: str) -> None:
    raw = value.encode("utf-8")
    _hash_write_u32(hasher, len(raw))
    hasher.update(raw)


def _hash_write_opt_str(hasher: "hashlib._Hash", value: str | None) -> None:
    if value is None:
        hasher.update(b"\x00")
        return
    hasher.update(b"\x01")
    _hash_write_str(hasher, value)


def _empty_snapshot_copy() -> dict[str, Any]:
    return _json_clone(EMPTY_SNAPSHOT_V1)


def _ledger_evidence() -> dict[str, list[Any]]:
    return {key: [] for key in EVIDENCE_KEYS_V0}


def _tx_order_inputs_for_case(case: dict[str, Any]) -> tuple[TxExecutionOrderInputV1, ...]:
    return tx_order_inputs_for_case_v1(case)


def _route_order_receipt_requirement_for_case(case: dict[str, Any]) -> Any | None:
    return route_order_receipt_requirement_for_case_v1(case)


def _proof_transactions_for_case(case: dict[str, Any]) -> list[Any]:
    proof_transactions = case.get("proof_transactions")
    if proof_transactions is None:
        proof_transactions = case["transactions"]
    if not isinstance(proof_transactions, list):
        raise TypeError("case.proof_transactions must be a list")
    return proof_transactions


def _transactions_hash_v0(*, view: str, transactions: list[Any]) -> str:
    return hash_v0(f"risc0_smoke_{view}_transactions_v0", transactions)


def _transaction_projection_binding_for_case(
    *,
    body_transactions: list[Any],
    proof_transactions: list[Any],
) -> dict[str, Any]:
    projected_transactions = list(project_route_body_transactions_to_proof_v1(body_transactions))
    projection_checked = projected_transactions == proof_transactions
    if not projection_checked:
        raise ValueError("proof_transactions must match deterministic body projection")
    return {
        "body_transactions_hash": _transactions_hash_v0(
            view="body",
            transactions=body_transactions,
        ),
        "proof_transactions_hash": _transactions_hash_v0(
            view="proof",
            transactions=proof_transactions,
        ),
        "proof_tx_count": len(proof_transactions),
        "proof_transactions_match_body": proof_transactions == body_transactions,
        "body_to_proof_projection_checked": True,
        "projection_contract": route_body_projection_contract_v1(),
        "projection_contract_hash": route_body_projection_contract_hash_v1(),
    }


def _apply_route_order_receipt_policy_to_body(body: dict[str, Any], case: dict[str, Any]) -> bool:
    expected = tx_order_inputs_for_case_v1(case)
    actual = tx_order_inputs_for_case_v1({"transactions": body.get("transactions", [])})
    if expected != actual:
        raise ValueError("body transactions must match case-derived tx_execution_order summary")
    return apply_route_order_receipt_policy_to_body_v1(body)


def _validate_body_order_receipt_matches_proof(body: dict[str, Any], proof: dict[str, Any]) -> bool:
    evidence = body.get("evidence")
    if not isinstance(evidence, dict):
        raise TypeError("body.evidence must be an object")
    proof_receipts = evidence.get("proof_receipts")
    if not isinstance(proof_receipts, list):
        raise TypeError("body.evidence.proof_receipts must be a list")
    meta = proof.get("meta")
    if not isinstance(meta, dict):
        raise TypeError("proof.meta must be an object")
    proof_type = proof.get("proof_type")
    proof_commitment = meta.get("tx_execution_order_commitment")
    matching: list[str] = []
    for receipt in proof_receipts:
        if not isinstance(receipt, dict):
            continue
        if receipt.get("schema") != "zenodex/zeno_ledger/risc0_tx_execution_order_commitment/v0":
            continue
        if receipt.get("proof_type") != proof_type:
            raise ValueError("body tx_execution_order receipt proof_type mismatch")
        commitment = receipt.get("tx_execution_order_commitment")
        if not isinstance(commitment, str):
            raise TypeError("body tx_execution_order receipt commitment must be a string")
        matching.append(commitment)
    if not matching:
        return False
    if len(matching) != 1:
        raise ValueError("body tx_execution_order receipt ambiguous")
    if matching[0].lower() != str(proof_commitment).lower():
        raise ValueError("body tx_execution_order receipt/proof meta mismatch")
    return True


def _apply_route_order_policy_to_context(context: dict[str, Any], case: dict[str, Any]) -> bool:
    requirement = _route_order_receipt_requirement_for_case(case)
    if requirement is None or not requirement.required:
        return False
    context.update(requirement.plan.context_patch())
    return True


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
    _apply_route_order_receipt_policy_to_body(body, case)
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
    body_transactions = body["transactions"]
    proof_transactions = _proof_transactions_for_case(case)
    projection_binding = _transaction_projection_binding_for_case(
        body_transactions=body_transactions,
        proof_transactions=proof_transactions,
    )
    body_tx_execution_order_commitment_checked = _validate_body_order_receipt_matches_proof(body, proof)
    header_unbound = _ledger_header_for_case(
        name=name,
        body=body,
        proof=proof,
        proof_journal_hash=ZERO_ROOT_V0,
    )
    metadata = build_risc0_proof_metadata_v0(
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

    meta = proof["meta"]
    assert isinstance(meta, dict)
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
    proof_transactions_path = out_dir / f"{name}_risc0_proof_transactions.json"
    body_path.write_text(json.dumps(body, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    header_path.write_text(json.dumps(header, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    metadata_path.write_text(json.dumps(metadata, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    proof_transactions_path.write_text(
        json.dumps(proof_transactions, sort_keys=True, indent=2) + "\n",
        encoding="utf-8",
    )

    return {
        "schema": "zenodex.risc0_real_proof_smoke.ledger_binding.v0",
        "ok": True,
        "header_bound": True,
        "body_checked": True,
        "body_tx_execution_order_commitment_checked": body_tx_execution_order_commitment_checked,
        "post_state_root_checked": post_state_root_checked,
        "pre_state_root_checked": pre_state_root_checked,
        "body_tx_count": len(body["transactions"]),
        "proof_tx_count": projection_binding["proof_tx_count"],
        "body_path": str(body_path),
        "header_path": str(header_path),
        "metadata_path": str(metadata_path),
        "proof_transactions_path": str(proof_transactions_path),
        "proof_journal_hash": proof_journal_hash,
        "body_transactions_hash": projection_binding["body_transactions_hash"],
        "proof_transactions_hash": projection_binding["proof_transactions_hash"],
        "proof_transactions_match_body": projection_binding["proof_transactions_match_body"],
        "body_to_proof_projection_checked": projection_binding["body_to_proof_projection_checked"],
        "projection_contract": projection_binding["projection_contract"],
        "projection_contract_hash": projection_binding["projection_contract_hash"],
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

    route_pre = _empty_snapshot_copy()
    route_pre["balances"] = [
        {"pubkey": SENDER, "asset": ASSET0, "amount": 10_000_000},
        {"pubkey": OTHER_SENDER, "asset": ASSET0, "amount": 10_000_000},
    ]
    route_pre["pools"] = [_pool_entry(reserve0=1_000_000, reserve1=1_000_000)]
    route_legs = [{"hops": [{"pool_id": POOL_ID}]}]
    route_quote_hash = _route_quote_receipt_hash_v1(
        kind="ROUTE_EXACT_IN",
        asset_in=ASSET0,
        asset_out=ASSET1,
        total_amount_in=100_000,
        total_min_amount_out=0,
        total_amount_out=0,
        total_max_amount_in=0,
        leg_indices=[0],
        legs=route_legs,
        pools_by_id={POOL_ID: route_pre["pools"][0]},
    )
    route_proof_tx = {
        "sender_pubkey": SENDER,
        "nonce": 0,
        "operations": {
            "2": [
                {
                    "module": "TauSwap",
                    "version": "v1",
                    "kind": "ROUTE_EXACT_IN",
                    "intent_id": "route-order-exec",
                    "sender_pubkey": SENDER,
                    "deadline": 100,
                    "quote_receipt_hash": route_quote_hash,
                    "quote_receipt": {
                        "body": {
                            "schema": "zenodex/route_quote_receipt/v1",
                            "kind": "exact_in",
                            "asset_in": ASSET0,
                            "asset_out": ASSET1,
                            "amount_in": 100_000,
                            "amount_out": 90_661,
                            "legs": route_legs,
                            "pools": {POOL_ID: "route-order-prestate-pool"},
                        },
                        "receipt_hash": route_quote_hash,
                    },
                    "asset_in": ASSET0,
                    "asset_out": ASSET1,
                    "leg_indices": [0],
                    "legs": route_legs,
                    "total_amount_in": 100_000,
                    "total_min_amount_out": 0,
                    "total_amount_out": 0,
                    "total_max_amount_in": 0,
                    "recipient": RECIPIENT,
                }
            ]
        },
    }
    route_body_tx = json.loads(json.dumps(route_proof_tx))
    route_body_tx["operations"] = {"5": [route_body_tx["operations"]["2"][0]]}
    route_writer_tx = json.loads(json.dumps(swap_tx))
    route_writer_tx["sender_pubkey"] = OTHER_SENDER
    route_writer_tx["operations"]["2"][0]["intent_id"] = "swap-order-exec"
    route_writer_tx["operations"]["2"][0]["sender_pubkey"] = OTHER_SENDER
    route_writer_tx["operations"]["2"][0]["amount_in"] = 100_000
    route_writer_tx["operations"]["2"][0]["min_amount_out"] = 0
    route_post = _empty_snapshot_copy()
    route_post["balances"] = [
        {"pubkey": SENDER, "asset": ASSET0, "amount": 9_900_000},
        {"pubkey": RECIPIENT, "asset": ASSET1, "amount": 166_230},
        {"pubkey": OTHER_SENDER, "asset": ASSET0, "amount": 9_900_000},
    ]
    route_post["pools"] = [_pool_entry(reserve0=1_200_000, reserve1=833_770)]

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
        "route_order": {
            "pre_snapshot": route_pre,
            "pre_hash": _snapshot_hash(route_pre),
            "transactions": [route_writer_tx, route_body_tx],
            "proof_transactions": list(
                project_route_body_transactions_to_proof_v1([route_writer_tx, route_body_tx])
            ),
            "post_hash": _snapshot_hash(route_post),
        },
    }


def _run_cli(
    *,
    repo: Path,
    request: dict[str, Any],
    target_dir: Path,
    timeout: int,
    cli_bin: Path | None,
    release: bool,
) -> dict[str, Any]:
    env = proof_runner_env(repo)
    env["RISC0_FORCE_BUILD"] = "1"
    env["CARGO_TARGET_DIR"] = str(target_dir)
    if cli_bin is not None:
        command = [str(cli_bin)]
    else:
        command = [
            "cargo",
            "run",
            "--manifest-path",
            str(repo / "zk/state_proof_risc0/Cargo.toml"),
            "-q",
            "-p",
            "tau-state-proof-risc0-cli",
        ]
        if release:
            command.append("--release")
    proc = subprocess.run(
        command,
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
            f"command={' '.join(command)}\n"
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
    cli_bin: Path | None,
    release: bool,
) -> dict[str, Any]:
    state_hash = "11" * 32
    app_state_pre = ""
    if case["pre_snapshot"] is not None:
        app_state_pre = _canonical_json_bytes(case["pre_snapshot"]).decode("utf-8")

    generate_context: dict[str, Any] = {
        "app_state_pre": app_state_pre,
        "app_hash_pre": case["pre_hash"],
        "chain_balances_post": {},
    }
    _apply_route_order_policy_to_context(generate_context, case)
    proof_transactions = _proof_transactions_for_case(case)
    generate_request = {
        "schema": "tau_state_proof_request",
        "schema_version": 1,
        "state_hash": state_hash,
        "block": {"header": {"timestamp": 1}, "transactions": proof_transactions},
        "tau_state": {"app_hash": case["post_hash"]},
        "context": generate_context,
    }
    started_generate = time.monotonic()
    proof = _run_cli(
        repo=repo,
        request=generate_request,
        target_dir=target_dir,
        timeout=timeout,
        cli_bin=cli_bin,
        release=release,
    )
    generate_seconds = round(time.monotonic() - started_generate, 3)
    proof_path = out_dir / f"{name}_tau_state_proof.json"
    proof_path.write_text(json.dumps(proof, sort_keys=True, indent=2) + "\n", encoding="utf-8")

    verify_context: dict[str, Any] = {
        "app_hash_pre": case["pre_hash"],
        "block_timestamp": 1,
    }
    _apply_route_order_policy_to_context(verify_context, case)
    verify_request = {
        "schema": "tau_state_proof_verify",
        "schema_version": 1,
        "state_hash": state_hash,
        "proof": proof,
        "block": {"header": {"timestamp": 1}, "transactions": proof_transactions},
        "tau_state": {"app_hash": case["post_hash"]},
        "context": verify_context,
    }
    started_verify = time.monotonic()
    verify = _run_cli(
        repo=repo,
        request=verify_request,
        target_dir=target_dir,
        timeout=timeout,
        cli_bin=cli_bin,
        release=release,
    )
    verify_seconds = round(time.monotonic() - started_verify, 3)
    if verify.get("ok") is not True:
        raise RuntimeError(f"receipt verification rejected: {verify}")

    meta_obj = proof.get("meta")
    if not isinstance(meta_obj, dict):
        raise RuntimeError("proof meta must be an object")
    meta: dict[str, Any] = meta_obj
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
        "generate_seconds": generate_seconds,
        "verify_seconds": verify_seconds,
        "total_seconds": round(generate_seconds + verify_seconds, 3),
        "runner_mode": "cli_bin" if cli_bin is not None else ("cargo_run_release" if release else "cargo_run_debug"),
        "ledger_binding": ledger_binding,
    }


def run_smoke(
    *,
    repo: Path,
    out_dir: Path,
    target_dir: Path,
    timeout: int,
    case_name: str,
    cli_bin: Path | None = None,
    release: bool = False,
) -> dict[str, Any]:
    out_dir.mkdir(parents=True, exist_ok=True)
    cases = _smoke_cases()
    default_cases = [name for name in cases if name != "route_order"]
    selected = default_cases if case_name == "all" else [case_name]
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
            cli_bin=cli_bin,
            release=release,
        )
        for index, name in enumerate(selected, start=1)
    ]

    report = {
        "schema": "zenodex.risc0_real_proof_smoke.v0",
        "ok": True,
        "runner_mode": "cli_bin" if cli_bin is not None else ("cargo_run_release" if release else "cargo_run_debug"),
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
        "--cli-bin",
        type=Path,
        help="Run a prebuilt tau-state-proof-risc0-cli binary instead of cargo run.",
    )
    parser.add_argument(
        "--release",
        action="store_true",
        help="Use cargo run --release when --cli-bin is not supplied.",
    )
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
            "route_order",
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
        cli_bin=args.cli_bin.resolve() if args.cli_bin is not None else None,
        release=bool(args.release),
    )
    print(json.dumps(report, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
