#!/usr/bin/env python3
"""Run real RISC0 proof smokes for the scoped zUSD mint transition.

The smoke proves `risc0.zenodex_zusd_transition.v1` through the unified
`tau-state-proof-risc0-cli` request/verify schema. It covers one oracle-bound
collateral deposit plus zUSD mint with MCR checks and zUSD balance/vault root
binding. It remains scoped testnet evidence and does not flip
`production_security_claim`.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import subprocess
from pathlib import Path
from typing import Any

PROOF_TYPE = "risc0.zenodex_zusd_transition.v1"
CHAIN_ID = "zenodex-local-risc0-smoke-1"
OWNER = "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
COLLATERAL_ASSET = "tAGRS"
E8 = 100_000_000
BPS_SCALE = 10_000


def _hex(label: str) -> str:
    return hashlib.sha256(label.encode("utf-8")).hexdigest()


def _u32(n: int) -> bytes:
    return int(n).to_bytes(4, "big", signed=False)


def _u64(n: int) -> bytes:
    return int(n).to_bytes(8, "big", signed=False)


def _u128(n: int) -> bytes:
    return int(n).to_bytes(16, "big", signed=False)


def _i128(n: int) -> bytes:
    return int(n).to_bytes(16, "big", signed=True)


def _write_str(h: "hashlib._Hash", value: str) -> None:
    raw = value.encode("utf-8")
    h.update(_u32(len(raw)))
    h.update(raw)


def _normalize_hex32(value: str) -> str:
    raw = str(value).strip().lower()
    if raw.startswith("0x"):
        raw = raw[2:]
    if len(raw) != 64:
        raise ValueError("expected 32-byte hex string")
    bytes.fromhex(raw)
    return raw


def _oracle(name: str, price_e8: int = E8, *, stale: bool = False) -> dict[str, Any]:
    price_ts = 10
    return {
        "oracle_bridge_id": f"zenodex-zusd-smoke-{name}",
        "oracle_bridge_hash": _hex(f"{name}:oracle_bridge"),
        "price_e8": int(price_e8),
        "price_timestamp": price_ts,
        "max_staleness_seconds": 5,
        "observed_at": price_ts + (6 if stale else 2),
        "pre_price_batch_commitment": _hex(f"{name}:pre_price_batch"),
    }


def _empty_snapshot() -> dict[str, Any]:
    return {
        "version": 1,
        "vaults": [],
        "balances": [],
        "total_debt_zusd_e8": 0,
    }


def _snapshot_hash(snapshot: dict[str, Any]) -> str:
    h = hashlib.sha256()
    h.update(b"zenodex.zusd.snapshot.v1:")
    h.update(_u32(int(snapshot["version"])))
    vaults = sorted(
        copy.deepcopy(snapshot.get("vaults", [])),
        key=lambda v: (str(v["pubkey"]), str(v["collateral_asset"])),
    )
    h.update(_u32(len(vaults)))
    for vault in vaults:
        _write_str(h, str(vault["pubkey"]))
        _write_str(h, str(vault["collateral_asset"]))
        h.update(_u128(int(vault["collateral_amount_e8"])))
        h.update(_u128(int(vault["debt_zusd_e8"])))
        h.update(_u64(int(vault["nonce"])))
    balances = sorted(copy.deepcopy(snapshot.get("balances", [])), key=lambda b: str(b["pubkey"]))
    h.update(_u32(len(balances)))
    for balance in balances:
        _write_str(h, str(balance["pubkey"]))
        h.update(_u128(int(balance["amount_e8"])))
    h.update(_u128(int(snapshot["total_debt_zusd_e8"])))
    return h.hexdigest()


def _balance_root(snapshot: dict[str, Any]) -> str:
    h = hashlib.sha256()
    h.update(b"zenodex.zusd.balance_root.v1:")
    balances = sorted(copy.deepcopy(snapshot.get("balances", [])), key=lambda b: str(b["pubkey"]))
    h.update(_u32(len(balances)))
    for balance in balances:
        _write_str(h, str(balance["pubkey"]))
        h.update(_u128(int(balance["amount_e8"])))
    return h.hexdigest()


def _vault_root(snapshot: dict[str, Any]) -> str:
    h = hashlib.sha256()
    h.update(b"zenodex.zusd.vault_root.v1:")
    vaults = sorted(
        copy.deepcopy(snapshot.get("vaults", [])),
        key=lambda v: (str(v["pubkey"]), str(v["collateral_asset"])),
    )
    h.update(_u32(len(vaults)))
    for vault in vaults:
        _write_str(h, str(vault["pubkey"]))
        _write_str(h, str(vault["collateral_asset"]))
        h.update(_u128(int(vault["collateral_amount_e8"])))
        h.update(_u128(int(vault["debt_zusd_e8"])))
        h.update(_u64(int(vault["nonce"])))
    return h.hexdigest()


def _participant_set_hash(participants: list[str]) -> str:
    values = sorted(set(str(p) for p in participants))
    h = hashlib.sha256()
    h.update(b"zenodex.participant_set.v1:")
    h.update(_u32(len(values)))
    for pubkey in values:
        _write_str(h, pubkey)
    return h.hexdigest()


def _hash_oracle_binding(h: "hashlib._Hash", oracle: dict[str, Any]) -> None:
    _write_str(h, str(oracle["oracle_bridge_id"]))
    _write_str(h, _normalize_hex32(str(oracle["oracle_bridge_hash"])))
    h.update(_i128(int(oracle["price_e8"])))
    h.update(_u64(int(oracle["price_timestamp"])))
    h.update(_u64(int(oracle["max_staleness_seconds"])))
    h.update(_u64(int(oracle["observed_at"])))
    _write_str(h, _normalize_hex32(str(oracle["pre_price_batch_commitment"])))


def _oracle_binding_hash(oracle: dict[str, Any]) -> str:
    h = hashlib.sha256()
    h.update(b"zenodex.oracle_binding.v1:")
    _hash_oracle_binding(h, oracle)
    return h.hexdigest()


def _operation_hash(operation: dict[str, Any]) -> str:
    h = hashlib.sha256()
    h.update(b"zenodex.zusd.operation.v1:")
    h.update(bytes([0]))
    _write_str(h, str(operation["pubkey"]))
    _write_str(h, str(operation["collateral_asset"]))
    h.update(_u128(int(operation["deposit_amount_e8"])))
    h.update(_u128(int(operation["mint_amount_e8"])))
    _hash_oracle_binding(h, operation["oracle"])
    h.update(_u32(int(operation["mcr_bps"])))
    h.update(_u64(int(operation["nonce"])))
    return h.hexdigest()


def _state_delta_hash(pre_hash: str, post_hash: str) -> str:
    h = hashlib.sha256()
    h.update(b"zenodex.state_delta.v1:")
    h.update(bytes.fromhex(pre_hash))
    h.update(bytes.fromhex(post_hash))
    return h.hexdigest()


def _apply_deposit_mint(pre_state: dict[str, Any], operation: dict[str, Any]) -> dict[str, Any]:
    post = copy.deepcopy(pre_state)
    key = (str(operation["pubkey"]), str(operation["collateral_asset"]))
    vaults = {
        (str(v["pubkey"]), str(v["collateral_asset"])): copy.deepcopy(v)
        for v in post.get("vaults", [])
    }
    vault = vaults.get(
        key,
        {
            "pubkey": key[0],
            "collateral_asset": key[1],
            "collateral_amount_e8": 0,
            "debt_zusd_e8": 0,
            "nonce": 0,
        },
    )
    vault["collateral_amount_e8"] = int(vault["collateral_amount_e8"]) + int(operation["deposit_amount_e8"])
    vault["debt_zusd_e8"] = int(vault["debt_zusd_e8"]) + int(operation["mint_amount_e8"])
    vault["nonce"] = int(operation["nonce"])
    vaults[key] = vault
    balances = {str(b["pubkey"]): int(b["amount_e8"]) for b in post.get("balances", [])}
    balances[key[0]] = balances.get(key[0], 0) + int(operation["mint_amount_e8"])
    post["vaults"] = sorted(vaults.values(), key=lambda v: (str(v["pubkey"]), str(v["collateral_asset"])))
    post["balances"] = [
        {"pubkey": pubkey, "amount_e8": amount}
        for pubkey, amount in sorted(balances.items())
        if amount != 0
    ]
    post["total_debt_zusd_e8"] = int(post["total_debt_zusd_e8"]) + int(operation["mint_amount_e8"])
    return post


def _mcr_ok(post_state: dict[str, Any], operation: dict[str, Any]) -> bool:
    vault = next(
        v
        for v in post_state["vaults"]
        if str(v["pubkey"]) == str(operation["pubkey"])
        and str(v["collateral_asset"]) == str(operation["collateral_asset"])
    )
    debt = int(vault["debt_zusd_e8"])
    if debt == 0:
        return True
    collateral = int(vault["collateral_amount_e8"])
    price = int(operation["oracle"]["price_e8"])
    mcr = int(operation["mcr_bps"])
    return collateral * price * BPS_SCALE >= debt * mcr * E8


def _case_input(
    name: str,
    *,
    pre_state: dict[str, Any] | None = None,
    deposit_amount_e8: int = 2_000 * E8,
    mint_amount_e8: int = 1_000 * E8,
    mcr_bps: int = 11_000,
    nonce: int = 1,
    stale_oracle: bool = False,
    expected_post_app_hash: str | None = None,
) -> dict[str, Any]:
    pre = copy.deepcopy(pre_state or _empty_snapshot())
    operation = {
        "kind": "deposit_mint",
        "pubkey": OWNER,
        "collateral_asset": COLLATERAL_ASSET,
        "deposit_amount_e8": int(deposit_amount_e8),
        "mint_amount_e8": int(mint_amount_e8),
        "oracle": _oracle(name, stale=stale_oracle),
        "mcr_bps": int(mcr_bps),
        "nonce": int(nonce),
    }
    post = _apply_deposit_mint(pre, operation)
    pre_hash = _snapshot_hash(pre)
    post_hash = _snapshot_hash(post)
    return {
        "pre_state": pre,
        "post_state": post,
        "operation": operation,
        "pre_app_hash": pre_hash,
        "post_app_hash": expected_post_app_hash or post_hash,
        "state_delta_hash": _state_delta_hash(pre_hash, post_hash),
        "operation_hash": _operation_hash(operation),
        "oracle_binding_hash": _oracle_binding_hash(operation["oracle"]),
        "zusd_balance_root_hash": _balance_root(post),
        "zusd_vault_root_hash": _vault_root(post),
        "participant_set_hash": _participant_set_hash([OWNER]),
        "minted_zusd_e8": int(operation["mint_amount_e8"]),
        "collateral_value_e8": int(post["vaults"][0]["collateral_amount_e8"]) * int(operation["oracle"]["price_e8"]) // E8,
        "mcr_ok": _mcr_ok(post, operation),
    }


def _cases() -> dict[str, dict[str, Any]]:
    pre_with_nonce = _empty_snapshot()
    pre_with_nonce["vaults"] = [
        {
            "pubkey": OWNER,
            "collateral_asset": COLLATERAL_ASSET,
            "collateral_amount_e8": 2_000 * E8,
            "debt_zusd_e8": 1_000 * E8,
            "nonce": 2,
        }
    ]
    pre_with_nonce["balances"] = [{"pubkey": OWNER, "amount_e8": 1_000 * E8}]
    pre_with_nonce["total_debt_zusd_e8"] = 1_000 * E8

    broken_debt = copy.deepcopy(pre_with_nonce)
    broken_debt["total_debt_zusd_e8"] = 1

    return {
        "mint": {"input": _case_input("mint"), "must_prove": True},
        "neg_mcr": {
            "input": _case_input("neg_mcr", deposit_amount_e8=1 * E8, mint_amount_e8=1_000 * E8),
            "must_prove": False,
        },
        "neg_stale_oracle": {
            "input": _case_input("neg_stale_oracle", stale_oracle=True),
            "must_prove": False,
        },
        "neg_nonce_replay": {
            "input": _case_input("neg_nonce_replay", pre_state=pre_with_nonce, nonce=2),
            "must_prove": False,
        },
        "neg_total_debt_mismatch": {
            "input": _case_input("neg_total_debt_mismatch", pre_state=broken_debt, nonce=3),
            "must_prove": False,
        },
        "neg_wrong_post_app_hash": {
            "input": _case_input("neg_wrong_post_app_hash", expected_post_app_hash=_hex("wrong-zusd-post")),
            "must_prove": False,
        },
    }


def _generate_request(name: str, case_input: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema": "tau_state_proof_request",
        "schema_version": 1,
        "proof_type": PROOF_TYPE,
        "state_hash": _hex(f"{name}:state_hash"),
        "chain_id": CHAIN_ID,
        "context": {
            "chain_id": CHAIN_ID,
            "execution_context_hash": _hex(f"{name}:execution_context"),
            "app_hash_pre": case_input["pre_app_hash"],
            "zusd_state_pre": case_input["pre_state"],
        },
        "pre_state": case_input["pre_state"],
        "operation": case_input["operation"],
        "expected_post_app_hash": case_input["post_app_hash"],
        "tau_state": {"app_hash": case_input["post_app_hash"]},
    }


def _run_cli(*, repo: Path, request: dict[str, Any], target_dir: Path, timeout: int) -> tuple[int, str, str]:
    env = os.environ.copy()
    env["RISC0_FORCE_BUILD"] = "1"
    env["CARGO_TARGET_DIR"] = str(target_dir)
    build = subprocess.run(
        [
            "cargo",
            "build",
            "--release",
            "--manifest-path",
            str(repo / "zk/state_proof_risc0/Cargo.toml"),
            "-q",
            "-p",
            "tau-state-proof-risc0-cli",
        ],
        cwd=repo,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=timeout,
        check=False,
    )
    if build.returncode != 0:
        return build.returncode, build.stdout, build.stderr
    cli_bin = target_dir / "release" / "tau-state-proof-risc0-cli"
    if not cli_bin.exists():
        return 2, "", f"missing built RISC0 CLI: {cli_bin}"
    command = [str(cli_bin)]
    if request.get("schema") == "tau_state_proof_verify":
        context = request.get("context")
        if not isinstance(context, dict):
            return 2, "", "verify context must be an object"
        expected_context_hash = context.get("execution_context_hash")
        if not isinstance(expected_context_hash, str) or not expected_context_hash:
            return 2, "", "verify execution_context_hash missing"
        command.extend(
            ["--expected-execution-context-hash", expected_context_hash]
        )
    proc = subprocess.run(
        command,
        cwd=repo,
        env=env,
        input=json.dumps(request, separators=(",", ":")),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=timeout,
        check=False,
    )
    return proc.returncode, proc.stdout, proc.stderr


def _run_cli_json(*, repo: Path, request: dict[str, Any], target_dir: Path, timeout: int) -> dict[str, Any]:
    rc, out, err = _run_cli(repo=repo, request=request, target_dir=target_dir, timeout=timeout)
    if rc != 0:
        raise RuntimeError(f"cli failed exit={rc}\nstdout={out[-2000:]}\nstderr={err[-4000:]}")
    parsed = json.loads(out)
    if not isinstance(parsed, dict):
        raise RuntimeError("cli returned non-object JSON")
    return parsed


def _verify(
    *,
    repo: Path,
    proof: dict[str, Any],
    expected: dict[str, Any],
    operation: dict[str, Any],
    target_dir: Path,
    timeout: int,
) -> dict[str, Any]:
    context = {
        "chain_id": expected["chain_id"],
        "execution_context_hash": expected["execution_context_hash"],
        "app_hash_pre": expected["pre_app_hash"],
        "operation_hash": expected["operation_hash"],
        "state_delta_hash": expected["state_delta_hash"],
        "oracle_binding_hash": expected["oracle_binding_hash"],
        "participant_set_hash": expected["participant_set_hash"],
        "zusd_balance_root_hash": expected["zusd_balance_root_hash"],
        "zusd_vault_root_hash": expected["zusd_vault_root_hash"],
    }
    return _run_cli_json(
        repo=repo,
        target_dir=target_dir,
        timeout=timeout,
        request={
            "schema": "tau_state_proof_verify",
            "schema_version": 1,
            "state_hash": proof["state_hash"],
            "chain_id": expected["chain_id"],
            "proof": proof,
            "tau_state": {"app_hash": expected["post_app_hash"]},
            "context": context,
            "operation": operation,
        },
    )


def _assert_verify_rejects(
    *,
    repo: Path,
    proof: dict[str, Any],
    expected: dict[str, Any],
    operation: dict[str, Any],
    target_dir: Path,
    timeout: int,
    label: str,
) -> str:
    result = _verify(
        repo=repo,
        proof=proof,
        expected=expected,
        operation=operation,
        target_dir=target_dir,
        timeout=timeout,
    )
    if result.get("ok") is not False:
        raise RuntimeError(f"{label}: verifier accepted tampered request: {result}")
    return str(result.get("error", ""))


def _expected_from_meta(meta: dict[str, Any]) -> dict[str, Any]:
    return {
        "execution_context_hash": meta["execution_context_hash"],
        "chain_id": meta["chain_id"],
        "pre_app_hash": meta["pre_app_hash"],
        "post_app_hash": meta["post_app_hash"],
        "operation_hash": meta["operation_hash"],
        "state_delta_hash": meta["state_delta_hash"],
        "oracle_binding_hash": meta["oracle_binding_hash"],
        "participant_set_hash": meta["participant_set_hash"],
        "zusd_balance_root_hash": meta["zusd_balance_root_hash"],
        "zusd_vault_root_hash": meta["zusd_vault_root_hash"],
    }


def _run_case(
    *,
    name: str,
    case: dict[str, Any],
    repo: Path,
    out_dir: Path,
    target_dir: Path,
    timeout: int,
) -> dict[str, Any]:
    case_input = case["input"]
    request = _generate_request(name, case_input)
    if not case["must_prove"]:
        rc, out, err = _run_cli(repo=repo, request=request, target_dir=target_dir, timeout=timeout)
        if rc == 0:
            raise RuntimeError(f"negative case {name} unexpectedly proved\nstdout={out[-2000:]}")
        return {
            "case": name,
            "kind": "negative",
            "ok": True,
            "rejected_as_expected": True,
            "exit_code": rc,
            "reject_signal": (err.strip().splitlines()[-1] if err.strip() else "")[:300],
        }

    proof = _run_cli_json(repo=repo, request=request, target_dir=target_dir, timeout=timeout)
    if proof.get("proof_type") != PROOF_TYPE:
        raise RuntimeError(f"{name}: wrong proof_type {proof.get('proof_type')}")
    meta = proof.get("meta")
    if not isinstance(meta, dict):
        raise RuntimeError(f"{name}: proof.meta missing")
    for key in (
        "pre_app_hash",
        "post_app_hash",
        "operation_hash",
        "state_delta_hash",
        "oracle_binding_hash",
        "zusd_balance_root_hash",
        "zusd_vault_root_hash",
        "participant_set_hash",
    ):
        if str(meta.get(key)) != str(case_input[key]):
            raise RuntimeError(f"{name}: meta {key} mismatch: {meta.get(key)} != {case_input[key]}")
    if str(meta.get("minted_zusd_e8")) != str(case_input["minted_zusd_e8"]):
        raise RuntimeError(f"{name}: minted_zusd_e8 mismatch")
    if str(meta.get("collateral_value_e8")) != str(case_input["collateral_value_e8"]):
        raise RuntimeError(f"{name}: collateral_value_e8 mismatch")

    expected = _expected_from_meta(meta)
    verified = _verify(
        repo=repo,
        proof=proof,
        expected=expected,
        operation=request["operation"],
        target_dir=target_dir,
        timeout=timeout,
    )
    if verified.get("ok") is not True:
        raise RuntimeError(f"{name}: strict verifier rejected proof: {verified}")

    tamper_errors: dict[str, str] = {}
    bad_proof = copy.deepcopy(proof)
    bad_proof["proof_type"] = "risc0.zenodex_perps_np_transition.v1"
    tamper_errors["wrong_proof_type"] = _assert_verify_rejects(
        repo=repo,
        proof=bad_proof,
        expected=expected,
        operation=request["operation"],
        target_dir=target_dir,
        timeout=timeout,
        label=f"{name}:wrong_proof_type",
    )
    bad_proof = copy.deepcopy(proof)
    bad_meta = bad_proof.setdefault("meta", {})
    if isinstance(bad_meta, dict):
        bad_meta["risc0_image_id"] = _hex(f"{name}-wrong-image-id")
    tamper_errors["wrong_image_id"] = _assert_verify_rejects(
        repo=repo,
        proof=bad_proof,
        expected=expected,
        operation=request["operation"],
        target_dir=target_dir,
        timeout=timeout,
        label=f"{name}:wrong_image_id",
    )
    for field, value in (
        ("chain_id", "wrong-chain"),
        ("pre_app_hash", _hex(f"{name}-wrong-pre-app")),
        ("post_app_hash", _hex(f"{name}-wrong-post-app")),
        ("operation_hash", _hex(f"{name}-wrong-operation")),
        ("oracle_binding_hash", _hex(f"{name}-wrong-oracle")),
        ("participant_set_hash", _hex(f"{name}-wrong-participants")),
        ("zusd_balance_root_hash", _hex(f"{name}-wrong-balance-root")),
        ("zusd_vault_root_hash", _hex(f"{name}-wrong-vault-root")),
        ("state_delta_hash", _hex(f"{name}-wrong-delta")),
    ):
        bad_expected = copy.deepcopy(expected)
        bad_expected[field] = value
        tamper_errors[field] = _assert_verify_rejects(
            repo=repo,
            proof=proof,
            expected=bad_expected,
            operation=request["operation"],
            target_dir=target_dir,
            timeout=timeout,
            label=f"{name}:{field}",
        )

    proof_path = out_dir / f"{name}_zusd_risc0_proof.json"
    proof_path.write_text(json.dumps(proof, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    return {
        "case": name,
        "kind": "positive",
        "ok": True,
        "proof_type": proof.get("proof_type"),
        "minted_zusd_e8": meta.get("minted_zusd_e8"),
        "collateral_value_e8": meta.get("collateral_value_e8"),
        "mcr_bps": meta.get("mcr_bps"),
        "risc0_image_id": meta.get("risc0_image_id"),
        "strict_verify": True,
        "tamper_rejections": sorted(tamper_errors),
        "proof_base64_len": len(proof.get("proof", "")) if isinstance(proof.get("proof"), str) else 0,
        "proof_path": str(proof_path),
    }


def run_smoke(*, repo: Path, out_dir: Path, target_dir: Path, timeout: int, case_name: str) -> dict[str, Any]:
    out_dir.mkdir(parents=True, exist_ok=True)
    target_dir.mkdir(parents=True, exist_ok=True)
    cases = _cases()
    selected = list(cases) if case_name == "all" else [case_name]
    unknown = [case for case in selected if case not in cases]
    if unknown:
        raise ValueError(f"unknown smoke case(s): {', '.join(unknown)}")
    reports = [
        _run_case(name=name, case=cases[name], repo=repo, out_dir=out_dir, target_dir=target_dir, timeout=timeout)
        for name in selected
    ]
    report = {
        "schema": "zenodex.zusd_risc0_real_proof_smoke_report.v1",
        "ok": all(bool(r.get("ok")) for r in reports),
        "proof_type": PROOF_TYPE,
        "case_count": len(reports),
        "positive": sum(1 for r in reports if r.get("kind") == "positive"),
        "negative": sum(1 for r in reports if r.get("kind") == "negative"),
        "production_security_claim": False,
        "cases": reports,
    }
    report_path = out_dir / "zusd_risc0_real_proof_smoke_report.json"
    report_path.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    return report


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--out-dir", type=Path, default=Path("/tmp/zenodex_zusd_risc0_smoke"))
    parser.add_argument("--target-dir", type=Path, default=Path("/tmp/zenodex_zusd_risc0_target"))
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--case", choices=tuple(list(_cases()) + ["all"]), default="mint")
    args = parser.parse_args()
    report = run_smoke(
        repo=args.repo.resolve(),
        out_dir=args.out_dir,
        target_dir=args.target_dir,
        timeout=args.timeout,
        case_name=args.case,
    )
    print(json.dumps(report, sort_keys=True, indent=2))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
